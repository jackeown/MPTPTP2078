%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:39 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 238 expanded)
%              Number of leaves         :   34 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 ( 847 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_369,plain,(
    ! [B_102,A_103] :
      ( l1_pre_topc(B_102)
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_381,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_369])).

tff(c_391,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_381])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_378,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_369])).

tff(c_388,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_378])).

tff(c_284,plain,(
    ! [B_89,A_90] :
      ( l1_pre_topc(B_89)
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_293,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_284])).

tff(c_303,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_293])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_287,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_284])).

tff(c_299,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_287])).

tff(c_62,plain,(
    ! [B_44,A_45] :
      ( l1_pre_topc(B_44)
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_65,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_77,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_65])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_81,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_71])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_84,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_74])).

tff(c_30,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_93,plain,(
    ! [B_49,A_50] :
      ( r1_tsep_1(B_49,A_50)
      | ~ r1_tsep_1(A_50,B_49)
      | ~ l1_struct_0(B_49)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_96,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_121,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_124,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_121])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_124])).

tff(c_129,plain,
    ( ~ l1_struct_0('#skF_6')
    | r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_131,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_134,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_134])).

tff(c_140,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_130,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_139,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_172,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_176,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(u1_struct_0(B_62),u1_struct_0(A_63))
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_172,c_12])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_179,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(u1_struct_0(A_68),u1_struct_0(B_69))
      | ~ r1_tsep_1(A_68,B_69)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_46,B_47] :
      ( ~ r1_xboole_0(A_46,B_47)
      | k3_xboole_0(A_46,B_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_194,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(u1_struct_0(A_74),u1_struct_0(B_75)) = k1_xboole_0
      | ~ r1_tsep_1(A_74,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_179,c_92])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r1_xboole_0(A_9,k3_xboole_0(B_10,C_11))
      | ~ r1_tarski(A_9,C_11)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_200,plain,(
    ! [A_9,B_75,A_74] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r1_tarski(A_9,u1_struct_0(B_75))
      | r1_xboole_0(A_9,u1_struct_0(A_74))
      | ~ r1_tsep_1(A_74,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_10])).

tff(c_215,plain,(
    ! [A_76,B_77,A_78] :
      ( ~ r1_tarski(A_76,u1_struct_0(B_77))
      | r1_xboole_0(A_76,u1_struct_0(A_78))
      | ~ r1_tsep_1(A_78,B_77)
      | ~ l1_struct_0(B_77)
      | ~ l1_struct_0(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_200])).

tff(c_219,plain,(
    ! [B_79,A_80,A_81] :
      ( r1_xboole_0(u1_struct_0(B_79),u1_struct_0(A_80))
      | ~ r1_tsep_1(A_80,A_81)
      | ~ l1_struct_0(A_81)
      | ~ l1_struct_0(A_80)
      | ~ m1_pre_topc(B_79,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_176,c_215])).

tff(c_221,plain,(
    ! [B_79] :
      ( r1_xboole_0(u1_struct_0(B_79),u1_struct_0('#skF_6'))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_79,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_139,c_219])).

tff(c_230,plain,(
    ! [B_82] :
      ( r1_xboole_0(u1_struct_0(B_82),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_82,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_140,c_130,c_221])).

tff(c_20,plain,(
    ! [A_18,B_20] :
      ( r1_tsep_1(A_18,B_20)
      | ~ r1_xboole_0(u1_struct_0(A_18),u1_struct_0(B_20))
      | ~ l1_struct_0(B_20)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_233,plain,(
    ! [B_82] :
      ( r1_tsep_1(B_82,'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0(B_82)
      | ~ m1_pre_topc(B_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_230,c_20])).

tff(c_252,plain,(
    ! [B_84] :
      ( r1_tsep_1(B_84,'#skF_6')
      | ~ l1_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_233])).

tff(c_28,plain,
    ( ~ r1_tsep_1('#skF_6','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_55,plain,(
    ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_259,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_252,c_55])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_259])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_271])).

tff(c_276,plain,(
    ~ r1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_277,plain,(
    r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_338,plain,(
    ! [B_98,A_99] :
      ( r1_tsep_1(B_98,A_99)
      | ~ r1_tsep_1(A_99,B_98)
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_340,plain,
    ( r1_tsep_1('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_338])).

tff(c_345,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_340])).

tff(c_347,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_350,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_347])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_350])).

tff(c_355,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_360,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_355])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_360])).

tff(c_366,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_365,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_421,plain,(
    ! [B_112,A_113] :
      ( r1_tsep_1(B_112,A_113)
      | ~ r1_tsep_1(A_113,B_112)
      | ~ l1_struct_0(B_112)
      | ~ l1_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_423,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_365,c_421])).

tff(c_426,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_423])).

tff(c_434,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_437,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_434])).

tff(c_441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_437])).

tff(c_442,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_446,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_442])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.32  
% 2.56/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.56/1.33  
% 2.56/1.33  %Foreground sorts:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Background operators:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Foreground operators:
% 2.56/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.56/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.33  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.56/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.33  
% 2.56/1.35  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 2.56/1.35  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.56/1.35  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.56/1.35  tff(f_89, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.56/1.35  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.56/1.35  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.35  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.56/1.35  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.56/1.35  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.56/1.35  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.56/1.35  tff(f_57, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.56/1.35  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_38, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_369, plain, (![B_102, A_103]: (l1_pre_topc(B_102) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.35  tff(c_381, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_369])).
% 2.56/1.35  tff(c_391, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_381])).
% 2.56/1.35  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.35  tff(c_34, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_378, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_369])).
% 2.56/1.35  tff(c_388, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_378])).
% 2.56/1.35  tff(c_284, plain, (![B_89, A_90]: (l1_pre_topc(B_89) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.35  tff(c_293, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_284])).
% 2.56/1.35  tff(c_303, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_293])).
% 2.56/1.35  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_287, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_284])).
% 2.56/1.35  tff(c_299, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_287])).
% 2.56/1.35  tff(c_62, plain, (![B_44, A_45]: (l1_pre_topc(B_44) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.35  tff(c_65, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_62])).
% 2.56/1.35  tff(c_77, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_65])).
% 2.56/1.35  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_71, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.56/1.35  tff(c_81, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_71])).
% 2.56/1.35  tff(c_74, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_62])).
% 2.56/1.35  tff(c_84, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_74])).
% 2.56/1.35  tff(c_30, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_54, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_30])).
% 2.56/1.35  tff(c_93, plain, (![B_49, A_50]: (r1_tsep_1(B_49, A_50) | ~r1_tsep_1(A_50, B_49) | ~l1_struct_0(B_49) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.56/1.35  tff(c_96, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_93])).
% 2.56/1.35  tff(c_121, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_96])).
% 2.56/1.35  tff(c_124, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_121])).
% 2.56/1.35  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_124])).
% 2.56/1.35  tff(c_129, plain, (~l1_struct_0('#skF_6') | r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_96])).
% 2.56/1.35  tff(c_131, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_129])).
% 2.56/1.35  tff(c_134, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_16, c_131])).
% 2.56/1.35  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_134])).
% 2.56/1.35  tff(c_140, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_129])).
% 2.56/1.35  tff(c_130, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_96])).
% 2.56/1.35  tff(c_139, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_129])).
% 2.56/1.35  tff(c_172, plain, (![B_62, A_63]: (m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.56/1.35  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.56/1.35  tff(c_176, plain, (![B_62, A_63]: (r1_tarski(u1_struct_0(B_62), u1_struct_0(A_63)) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_172, c_12])).
% 2.56/1.35  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.35  tff(c_179, plain, (![A_68, B_69]: (r1_xboole_0(u1_struct_0(A_68), u1_struct_0(B_69)) | ~r1_tsep_1(A_68, B_69) | ~l1_struct_0(B_69) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.35  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.35  tff(c_87, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.35  tff(c_92, plain, (![A_46, B_47]: (~r1_xboole_0(A_46, B_47) | k3_xboole_0(A_46, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.56/1.35  tff(c_194, plain, (![A_74, B_75]: (k3_xboole_0(u1_struct_0(A_74), u1_struct_0(B_75))=k1_xboole_0 | ~r1_tsep_1(A_74, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_74))), inference(resolution, [status(thm)], [c_179, c_92])).
% 2.56/1.35  tff(c_10, plain, (![A_9, B_10, C_11]: (~r1_xboole_0(A_9, k3_xboole_0(B_10, C_11)) | ~r1_tarski(A_9, C_11) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.35  tff(c_200, plain, (![A_9, B_75, A_74]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r1_tarski(A_9, u1_struct_0(B_75)) | r1_xboole_0(A_9, u1_struct_0(A_74)) | ~r1_tsep_1(A_74, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_194, c_10])).
% 2.56/1.35  tff(c_215, plain, (![A_76, B_77, A_78]: (~r1_tarski(A_76, u1_struct_0(B_77)) | r1_xboole_0(A_76, u1_struct_0(A_78)) | ~r1_tsep_1(A_78, B_77) | ~l1_struct_0(B_77) | ~l1_struct_0(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_200])).
% 2.56/1.35  tff(c_219, plain, (![B_79, A_80, A_81]: (r1_xboole_0(u1_struct_0(B_79), u1_struct_0(A_80)) | ~r1_tsep_1(A_80, A_81) | ~l1_struct_0(A_81) | ~l1_struct_0(A_80) | ~m1_pre_topc(B_79, A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_176, c_215])).
% 2.56/1.35  tff(c_221, plain, (![B_79]: (r1_xboole_0(u1_struct_0(B_79), u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6') | ~m1_pre_topc(B_79, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_139, c_219])).
% 2.56/1.35  tff(c_230, plain, (![B_82]: (r1_xboole_0(u1_struct_0(B_82), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_82, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_140, c_130, c_221])).
% 2.56/1.35  tff(c_20, plain, (![A_18, B_20]: (r1_tsep_1(A_18, B_20) | ~r1_xboole_0(u1_struct_0(A_18), u1_struct_0(B_20)) | ~l1_struct_0(B_20) | ~l1_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.35  tff(c_233, plain, (![B_82]: (r1_tsep_1(B_82, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(B_82) | ~m1_pre_topc(B_82, '#skF_5'))), inference(resolution, [status(thm)], [c_230, c_20])).
% 2.56/1.35  tff(c_252, plain, (![B_84]: (r1_tsep_1(B_84, '#skF_6') | ~l1_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_233])).
% 2.56/1.35  tff(c_28, plain, (~r1_tsep_1('#skF_6', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.56/1.35  tff(c_55, plain, (~r1_tsep_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_28])).
% 2.56/1.35  tff(c_259, plain, (~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_252, c_55])).
% 2.56/1.35  tff(c_268, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_259])).
% 2.56/1.35  tff(c_271, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_268])).
% 2.56/1.35  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_271])).
% 2.56/1.35  tff(c_276, plain, (~r1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.56/1.35  tff(c_277, plain, (r1_tsep_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_28])).
% 2.56/1.35  tff(c_338, plain, (![B_98, A_99]: (r1_tsep_1(B_98, A_99) | ~r1_tsep_1(A_99, B_98) | ~l1_struct_0(B_98) | ~l1_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.56/1.35  tff(c_340, plain, (r1_tsep_1('#skF_6', '#skF_4') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_277, c_338])).
% 2.56/1.35  tff(c_345, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_276, c_340])).
% 2.56/1.35  tff(c_347, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_345])).
% 2.56/1.35  tff(c_350, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_347])).
% 2.56/1.35  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_350])).
% 2.56/1.35  tff(c_355, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_345])).
% 2.56/1.35  tff(c_360, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_16, c_355])).
% 2.56/1.35  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_303, c_360])).
% 2.56/1.35  tff(c_366, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 2.56/1.35  tff(c_365, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.56/1.35  tff(c_421, plain, (![B_112, A_113]: (r1_tsep_1(B_112, A_113) | ~r1_tsep_1(A_113, B_112) | ~l1_struct_0(B_112) | ~l1_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.56/1.35  tff(c_423, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_365, c_421])).
% 2.56/1.35  tff(c_426, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_366, c_423])).
% 2.56/1.35  tff(c_434, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_426])).
% 2.56/1.35  tff(c_437, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_16, c_434])).
% 2.56/1.35  tff(c_441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_388, c_437])).
% 2.56/1.35  tff(c_442, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_426])).
% 2.56/1.35  tff(c_446, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_442])).
% 2.56/1.35  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_391, c_446])).
% 2.56/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  Inference rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Ref     : 0
% 2.56/1.35  #Sup     : 69
% 2.56/1.35  #Fact    : 0
% 2.56/1.35  #Define  : 0
% 2.56/1.35  #Split   : 8
% 2.56/1.35  #Chain   : 0
% 2.56/1.35  #Close   : 0
% 2.56/1.35  
% 2.56/1.35  Ordering : KBO
% 2.56/1.35  
% 2.56/1.35  Simplification rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Subsume      : 3
% 2.56/1.35  #Demod        : 41
% 2.56/1.35  #Tautology    : 21
% 2.56/1.35  #SimpNegUnit  : 4
% 2.56/1.35  #BackRed      : 0
% 2.56/1.35  
% 2.56/1.35  #Partial instantiations: 0
% 2.56/1.35  #Strategies tried      : 1
% 2.56/1.35  
% 2.56/1.35  Timing (in seconds)
% 2.56/1.35  ----------------------
% 2.56/1.35  Preprocessing        : 0.30
% 2.56/1.35  Parsing              : 0.17
% 2.56/1.35  CNF conversion       : 0.02
% 2.56/1.35  Main loop            : 0.26
% 2.56/1.35  Inferencing          : 0.11
% 2.56/1.35  Reduction            : 0.07
% 2.56/1.35  Demodulation         : 0.05
% 2.56/1.35  BG Simplification    : 0.01
% 2.56/1.35  Subsumption          : 0.04
% 2.56/1.35  Abstraction          : 0.01
% 2.56/1.35  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.61
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
