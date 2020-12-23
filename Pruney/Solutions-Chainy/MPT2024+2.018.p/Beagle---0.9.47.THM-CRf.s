%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:16 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 426 expanded)
%              Number of leaves         :   29 ( 178 expanded)
%              Depth                    :   17
%              Number of atoms          :  199 (1670 expanded)
%              Number of equality atoms :    9 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_115,plain,(
    ! [A_82,B_83,C_84] :
      ( '#skF_3'(A_82,B_83,C_84) = C_84
      | ~ m1_subset_1(C_84,u1_struct_0(k9_yellow_6(A_82,B_83)))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_121,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_128,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_121])).

tff(c_129,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_128])).

tff(c_244,plain,(
    ! [B_94,A_95,C_96] :
      ( r2_hidden(B_94,'#skF_3'(A_95,B_94,C_96))
      | ~ m1_subset_1(C_96,u1_struct_0(k9_yellow_6(A_95,B_94)))
      | ~ m1_subset_1(B_94,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_248,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_244])).

tff(c_255,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_129,c_248])).

tff(c_256,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_255])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_630,plain,(
    ! [A_120,B_121,C_122] :
      ( m1_subset_1('#skF_3'(A_120,B_121,C_122),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(C_122,u1_struct_0(k9_yellow_6(A_120,B_121)))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_636,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_630])).

tff(c_642,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_636])).

tff(c_643,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_642])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_650,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_643,c_24])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_118,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_124,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_118])).

tff(c_125,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_124])).

tff(c_639,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_630])).

tff(c_645,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_639])).

tff(c_646,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_645])).

tff(c_654,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_646,c_24])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k2_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(C_9,B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_231,plain,(
    ! [A_91,B_92,C_93] :
      ( v3_pre_topc('#skF_3'(A_91,B_92,C_93),A_91)
      | ~ m1_subset_1(C_93,u1_struct_0(k9_yellow_6(A_91,B_92)))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_235,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_231])).

tff(c_242,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_129,c_235])).

tff(c_243,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_242])).

tff(c_233,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_231])).

tff(c_238,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_125,c_233])).

tff(c_239,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_238])).

tff(c_892,plain,(
    ! [B_134,C_135,A_136] :
      ( v3_pre_topc(k2_xboole_0(B_134,C_135),A_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v3_pre_topc(C_135,A_136)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v3_pre_topc(B_134,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_900,plain,(
    ! [B_134] :
      ( v3_pre_topc(k2_xboole_0(B_134,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_134,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_646,c_892])).

tff(c_918,plain,(
    ! [B_137] :
      ( v3_pre_topc(k2_xboole_0(B_137,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_137,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_239,c_900])).

tff(c_932,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_643,c_918])).

tff(c_948,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_932])).

tff(c_997,plain,(
    ! [C_140,A_141,B_142] :
      ( r2_hidden(C_140,u1_struct_0(k9_yellow_6(A_141,B_142)))
      | ~ v3_pre_topc(C_140,A_141)
      | ~ r2_hidden(B_142,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4582,plain,(
    ! [C_292,A_293,B_294] :
      ( m1_subset_1(C_292,u1_struct_0(k9_yellow_6(A_293,B_294)))
      | ~ v3_pre_topc(C_292,A_293)
      | ~ r2_hidden(B_294,C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ m1_subset_1(B_294,u1_struct_0(A_293))
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_997,c_22])).

tff(c_44,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4592,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4582,c_44])).

tff(c_4598,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_948,c_4592])).

tff(c_4599,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4598])).

tff(c_4600,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_4599])).

tff(c_4604,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_4600])).

tff(c_4607,plain,
    ( ~ r1_tarski('#skF_7',u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_4604])).

tff(c_4611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_654,c_4607])).

tff(c_4612,plain,(
    ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4599])).

tff(c_4616,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_4612])).

tff(c_4623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_4616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.46  
% 6.77/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.46  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.77/2.46  
% 6.77/2.46  %Foreground sorts:
% 6.77/2.46  
% 6.77/2.46  
% 6.77/2.46  %Background operators:
% 6.77/2.46  
% 6.77/2.46  
% 6.77/2.46  %Foreground operators:
% 6.77/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.77/2.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.77/2.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.77/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.77/2.46  tff('#skF_7', type, '#skF_7': $i).
% 6.77/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.77/2.46  tff('#skF_6', type, '#skF_6': $i).
% 6.77/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.77/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.46  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 6.77/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.77/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.77/2.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.77/2.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.77/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.46  
% 6.77/2.48  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 6.77/2.48  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 6.77/2.48  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.77/2.48  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.77/2.48  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.77/2.48  tff(f_62, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 6.77/2.48  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 6.77/2.48  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.77/2.48  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_115, plain, (![A_82, B_83, C_84]: ('#skF_3'(A_82, B_83, C_84)=C_84 | ~m1_subset_1(C_84, u1_struct_0(k9_yellow_6(A_82, B_83))) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.48  tff(c_121, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_115])).
% 6.77/2.48  tff(c_128, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_121])).
% 6.77/2.48  tff(c_129, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_56, c_128])).
% 6.77/2.48  tff(c_244, plain, (![B_94, A_95, C_96]: (r2_hidden(B_94, '#skF_3'(A_95, B_94, C_96)) | ~m1_subset_1(C_96, u1_struct_0(k9_yellow_6(A_95, B_94))) | ~m1_subset_1(B_94, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.48  tff(c_248, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_244])).
% 6.77/2.48  tff(c_255, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_129, c_248])).
% 6.77/2.48  tff(c_256, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_255])).
% 6.77/2.48  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.77/2.48  tff(c_630, plain, (![A_120, B_121, C_122]: (m1_subset_1('#skF_3'(A_120, B_121, C_122), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(C_122, u1_struct_0(k9_yellow_6(A_120, B_121))) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.48  tff(c_636, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_630])).
% 6.77/2.48  tff(c_642, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_636])).
% 6.77/2.48  tff(c_643, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_642])).
% 6.77/2.48  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.77/2.48  tff(c_650, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_643, c_24])).
% 6.77/2.48  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_118, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_115])).
% 6.77/2.48  tff(c_124, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_118])).
% 6.77/2.48  tff(c_125, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_56, c_124])).
% 6.77/2.48  tff(c_639, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_125, c_630])).
% 6.77/2.48  tff(c_645, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_639])).
% 6.77/2.48  tff(c_646, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_645])).
% 6.77/2.48  tff(c_654, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_646, c_24])).
% 6.77/2.48  tff(c_20, plain, (![A_7, C_9, B_8]: (r1_tarski(k2_xboole_0(A_7, C_9), B_8) | ~r1_tarski(C_9, B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.77/2.48  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.77/2.48  tff(c_231, plain, (![A_91, B_92, C_93]: (v3_pre_topc('#skF_3'(A_91, B_92, C_93), A_91) | ~m1_subset_1(C_93, u1_struct_0(k9_yellow_6(A_91, B_92))) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.48  tff(c_235, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_231])).
% 6.77/2.48  tff(c_242, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_129, c_235])).
% 6.77/2.48  tff(c_243, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_242])).
% 6.77/2.48  tff(c_233, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_231])).
% 6.77/2.48  tff(c_238, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_125, c_233])).
% 6.77/2.48  tff(c_239, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_238])).
% 6.77/2.48  tff(c_892, plain, (![B_134, C_135, A_136]: (v3_pre_topc(k2_xboole_0(B_134, C_135), A_136) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~v3_pre_topc(C_135, A_136) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_136))) | ~v3_pre_topc(B_134, A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.77/2.48  tff(c_900, plain, (![B_134]: (v3_pre_topc(k2_xboole_0(B_134, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_134, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_646, c_892])).
% 6.77/2.48  tff(c_918, plain, (![B_137]: (v3_pre_topc(k2_xboole_0(B_137, '#skF_7'), '#skF_4') | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_239, c_900])).
% 6.77/2.48  tff(c_932, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_643, c_918])).
% 6.77/2.48  tff(c_948, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_932])).
% 6.77/2.48  tff(c_997, plain, (![C_140, A_141, B_142]: (r2_hidden(C_140, u1_struct_0(k9_yellow_6(A_141, B_142))) | ~v3_pre_topc(C_140, A_141) | ~r2_hidden(B_142, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.77/2.48  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.77/2.48  tff(c_4582, plain, (![C_292, A_293, B_294]: (m1_subset_1(C_292, u1_struct_0(k9_yellow_6(A_293, B_294))) | ~v3_pre_topc(C_292, A_293) | ~r2_hidden(B_294, C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(u1_struct_0(A_293))) | ~m1_subset_1(B_294, u1_struct_0(A_293)) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(resolution, [status(thm)], [c_997, c_22])).
% 6.77/2.48  tff(c_44, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.77/2.48  tff(c_4592, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4582, c_44])).
% 6.77/2.48  tff(c_4598, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_948, c_4592])).
% 6.77/2.48  tff(c_4599, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_4598])).
% 6.77/2.48  tff(c_4600, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_4599])).
% 6.77/2.48  tff(c_4604, plain, (~r1_tarski(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_4600])).
% 6.77/2.48  tff(c_4607, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_4')) | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_4604])).
% 6.77/2.48  tff(c_4611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_650, c_654, c_4607])).
% 6.77/2.48  tff(c_4612, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_4599])).
% 6.77/2.48  tff(c_4616, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_4612])).
% 6.77/2.48  tff(c_4623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_4616])).
% 6.77/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.48  
% 6.77/2.48  Inference rules
% 6.77/2.48  ----------------------
% 6.77/2.48  #Ref     : 0
% 6.77/2.48  #Sup     : 917
% 6.77/2.48  #Fact    : 16
% 6.77/2.48  #Define  : 0
% 6.77/2.48  #Split   : 1
% 6.77/2.48  #Chain   : 0
% 6.77/2.48  #Close   : 0
% 6.77/2.48  
% 6.77/2.48  Ordering : KBO
% 6.77/2.48  
% 6.77/2.48  Simplification rules
% 6.77/2.48  ----------------------
% 6.77/2.48  #Subsume      : 196
% 6.77/2.48  #Demod        : 465
% 6.77/2.48  #Tautology    : 168
% 6.77/2.48  #SimpNegUnit  : 13
% 6.77/2.48  #BackRed      : 7
% 6.77/2.48  
% 6.77/2.48  #Partial instantiations: 0
% 6.77/2.48  #Strategies tried      : 1
% 6.77/2.48  
% 6.77/2.48  Timing (in seconds)
% 6.77/2.48  ----------------------
% 6.77/2.48  Preprocessing        : 0.41
% 6.77/2.48  Parsing              : 0.23
% 6.77/2.48  CNF conversion       : 0.03
% 6.77/2.48  Main loop            : 1.21
% 6.77/2.48  Inferencing          : 0.40
% 6.77/2.48  Reduction            : 0.34
% 6.77/2.48  Demodulation         : 0.25
% 6.77/2.48  BG Simplification    : 0.05
% 6.77/2.48  Subsumption          : 0.33
% 6.77/2.48  Abstraction          : 0.07
% 6.77/2.48  MUC search           : 0.00
% 6.77/2.48  Cooper               : 0.00
% 6.77/2.48  Total                : 1.66
% 6.77/2.48  Index Insertion      : 0.00
% 6.77/2.48  Index Deletion       : 0.00
% 6.77/2.48  Index Matching       : 0.00
% 6.77/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
