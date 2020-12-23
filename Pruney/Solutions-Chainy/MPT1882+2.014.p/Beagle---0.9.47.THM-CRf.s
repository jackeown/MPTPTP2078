%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:14 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 405 expanded)
%              Number of leaves         :   34 ( 149 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 (1490 expanded)
%              Number of equality atoms :   29 (  99 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_mcart_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_105,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_68,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [B_63] : k4_xboole_0(B_63,B_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [B_64] : r1_tarski(k1_xboole_0,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_12])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [B_64] : k4_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_132,c_10])).

tff(c_66,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_73,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60])).

tff(c_14,plain,(
    ! [A_7] :
      ( v1_zfmisc_1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_449,plain,(
    ! [A_115,B_116] :
      ( '#skF_2'(A_115,B_116) != B_116
      | v3_tex_2(B_116,A_115)
      | ~ v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_456,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_449])).

tff(c_460,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_456])).

tff(c_461,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_460])).

tff(c_462,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1010,plain,(
    ! [B_141,A_142] :
      ( v2_tex_2(B_141,A_142)
      | ~ v1_zfmisc_1(B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | v1_xboole_0(B_141)
      | ~ l1_pre_topc(A_142)
      | ~ v2_tdlat_3(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1017,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1010])).

tff(c_1021,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_70,c_1017])).

tff(c_1023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_462,c_1021])).

tff(c_1024,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_1025,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_1097,plain,(
    ! [B_152,A_153] :
      ( r1_tarski(B_152,'#skF_2'(A_153,B_152))
      | v3_tex_2(B_152,A_153)
      | ~ v2_tex_2(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1102,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1097])).

tff(c_1106,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1025,c_1102])).

tff(c_1107,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1106])).

tff(c_42,plain,(
    ! [B_44,A_42] :
      ( B_44 = A_42
      | ~ r1_tarski(A_42,B_44)
      | ~ v1_zfmisc_1(B_44)
      | v1_xboole_0(B_44)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1116,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1107,c_42])).

tff(c_1128,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1024,c_1116])).

tff(c_1137,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1128])).

tff(c_1141,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_1137])).

tff(c_1053,plain,(
    ! [A_145,B_146] :
      ( v2_tex_2('#skF_2'(A_145,B_146),A_145)
      | v3_tex_2(B_146,A_145)
      | ~ v2_tex_2(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1058,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1053])).

tff(c_1062,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1025,c_1058])).

tff(c_1063,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1062])).

tff(c_36,plain,(
    ! [A_32,B_38] :
      ( m1_subset_1('#skF_2'(A_32,B_38),k1_zfmisc_1(u1_struct_0(A_32)))
      | v3_tex_2(B_38,A_32)
      | ~ v2_tex_2(B_38,A_32)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1683,plain,(
    ! [B_169,A_170] :
      ( v1_zfmisc_1(B_169)
      | ~ v2_tex_2(B_169,A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | v1_xboole_0(B_169)
      | ~ l1_pre_topc(A_170)
      | ~ v2_tdlat_3(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_9459,plain,(
    ! [A_324,B_325] :
      ( v1_zfmisc_1('#skF_2'(A_324,B_325))
      | ~ v2_tex_2('#skF_2'(A_324,B_325),A_324)
      | v1_xboole_0('#skF_2'(A_324,B_325))
      | ~ v2_tdlat_3(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324)
      | v3_tex_2(B_325,A_324)
      | ~ v2_tex_2(B_325,A_324)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324) ) ),
    inference(resolution,[status(thm)],[c_36,c_1683])).

tff(c_9465,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1063,c_9459])).

tff(c_9470,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1025,c_56,c_54,c_9465])).

tff(c_9472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_58,c_1141,c_1137,c_9470])).

tff(c_9473,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_255,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_292,plain,(
    ! [B_77,A_78,A_79] :
      ( ~ v1_xboole_0(B_77)
      | ~ r2_hidden(A_78,A_79)
      | ~ r1_tarski(A_79,B_77) ) ),
    inference(resolution,[status(thm)],[c_18,c_255])).

tff(c_300,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r1_tarski(A_86,B_85)
      | k1_xboole_0 = A_86 ) ),
    inference(resolution,[status(thm)],[c_22,c_292])).

tff(c_321,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_300])).

tff(c_9484,plain,(
    '#skF_2'('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9473,c_321])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_1110,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | k4_xboole_0('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1107,c_170])).

tff(c_1124,plain,(
    k4_xboole_0('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1024,c_1110])).

tff(c_9491,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9484,c_1124])).

tff(c_9499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_9491])).

tff(c_9501,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_9500,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_9825,plain,(
    ! [B_376,A_377] :
      ( v2_tex_2(B_376,A_377)
      | ~ v3_tex_2(B_376,A_377)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9832,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_9825])).

tff(c_9836,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9500,c_9832])).

tff(c_10284,plain,(
    ! [B_425,A_426] :
      ( v1_zfmisc_1(B_425)
      | ~ v2_tex_2(B_425,A_426)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_426)))
      | v1_xboole_0(B_425)
      | ~ l1_pre_topc(A_426)
      | ~ v2_tdlat_3(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10291,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_10284])).

tff(c_10295,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_9836,c_10291])).

tff(c_10297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_9501,c_10295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.58  
% 7.18/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.58  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_mcart_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 7.18/2.58  
% 7.18/2.58  %Foreground sorts:
% 7.18/2.58  
% 7.18/2.58  
% 7.18/2.58  %Background operators:
% 7.18/2.58  
% 7.18/2.58  
% 7.18/2.58  %Foreground operators:
% 7.18/2.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.18/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.18/2.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.18/2.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.18/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.18/2.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.18/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.18/2.58  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.18/2.58  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.18/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.18/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.18/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.18/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.18/2.58  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.18/2.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.18/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.18/2.58  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.18/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.18/2.58  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 7.18/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.18/2.58  
% 7.58/2.61  tff(f_144, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 7.58/2.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.58/2.61  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.58/2.61  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.58/2.61  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 7.58/2.61  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 7.58/2.61  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 7.58/2.61  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 7.58/2.61  tff(f_68, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 7.58/2.61  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.58/2.61  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.58/2.61  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.58/2.61  tff(c_93, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.58/2.61  tff(c_121, plain, (![B_63]: (k4_xboole_0(B_63, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_93])).
% 7.58/2.61  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.58/2.61  tff(c_132, plain, (![B_64]: (r1_tarski(k1_xboole_0, B_64))), inference(superposition, [status(thm), theory('equality')], [c_121, c_12])).
% 7.58/2.61  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.58/2.61  tff(c_136, plain, (![B_64]: (k4_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_132, c_10])).
% 7.58/2.61  tff(c_66, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_70, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 7.58/2.61  tff(c_60, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_73, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60])).
% 7.58/2.61  tff(c_14, plain, (![A_7]: (v1_zfmisc_1(A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.58/2.61  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_449, plain, (![A_115, B_116]: ('#skF_2'(A_115, B_116)!=B_116 | v3_tex_2(B_116, A_115) | ~v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.58/2.61  tff(c_456, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_449])).
% 7.58/2.61  tff(c_460, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_456])).
% 7.58/2.61  tff(c_461, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_73, c_460])).
% 7.58/2.61  tff(c_462, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_461])).
% 7.58/2.61  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_54, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.58/2.61  tff(c_1010, plain, (![B_141, A_142]: (v2_tex_2(B_141, A_142) | ~v1_zfmisc_1(B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | v1_xboole_0(B_141) | ~l1_pre_topc(A_142) | ~v2_tdlat_3(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.61  tff(c_1017, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1010])).
% 7.58/2.61  tff(c_1021, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_70, c_1017])).
% 7.58/2.61  tff(c_1023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_462, c_1021])).
% 7.58/2.61  tff(c_1024, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_461])).
% 7.58/2.61  tff(c_1025, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_461])).
% 7.58/2.61  tff(c_1097, plain, (![B_152, A_153]: (r1_tarski(B_152, '#skF_2'(A_153, B_152)) | v3_tex_2(B_152, A_153) | ~v2_tex_2(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.58/2.61  tff(c_1102, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1097])).
% 7.58/2.61  tff(c_1106, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1025, c_1102])).
% 7.58/2.61  tff(c_1107, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_73, c_1106])).
% 7.58/2.61  tff(c_42, plain, (![B_44, A_42]: (B_44=A_42 | ~r1_tarski(A_42, B_44) | ~v1_zfmisc_1(B_44) | v1_xboole_0(B_44) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.58/2.61  tff(c_1116, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1107, c_42])).
% 7.58/2.61  tff(c_1128, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_1024, c_1116])).
% 7.58/2.61  tff(c_1137, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1128])).
% 7.58/2.61  tff(c_1141, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_1137])).
% 7.58/2.61  tff(c_1053, plain, (![A_145, B_146]: (v2_tex_2('#skF_2'(A_145, B_146), A_145) | v3_tex_2(B_146, A_145) | ~v2_tex_2(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.58/2.61  tff(c_1058, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1053])).
% 7.58/2.61  tff(c_1062, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1025, c_1058])).
% 7.58/2.61  tff(c_1063, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_73, c_1062])).
% 7.58/2.61  tff(c_36, plain, (![A_32, B_38]: (m1_subset_1('#skF_2'(A_32, B_38), k1_zfmisc_1(u1_struct_0(A_32))) | v3_tex_2(B_38, A_32) | ~v2_tex_2(B_38, A_32) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.58/2.61  tff(c_1683, plain, (![B_169, A_170]: (v1_zfmisc_1(B_169) | ~v2_tex_2(B_169, A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | v1_xboole_0(B_169) | ~l1_pre_topc(A_170) | ~v2_tdlat_3(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.61  tff(c_9459, plain, (![A_324, B_325]: (v1_zfmisc_1('#skF_2'(A_324, B_325)) | ~v2_tex_2('#skF_2'(A_324, B_325), A_324) | v1_xboole_0('#skF_2'(A_324, B_325)) | ~v2_tdlat_3(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324) | v3_tex_2(B_325, A_324) | ~v2_tex_2(B_325, A_324) | ~m1_subset_1(B_325, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324))), inference(resolution, [status(thm)], [c_36, c_1683])).
% 7.58/2.61  tff(c_9465, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1063, c_9459])).
% 7.58/2.61  tff(c_9470, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1025, c_56, c_54, c_9465])).
% 7.58/2.61  tff(c_9472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_58, c_1141, c_1137, c_9470])).
% 7.58/2.61  tff(c_9473, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1128])).
% 7.58/2.61  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.58/2.61  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.58/2.61  tff(c_255, plain, (![C_72, B_73, A_74]: (~v1_xboole_0(C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.58/2.61  tff(c_292, plain, (![B_77, A_78, A_79]: (~v1_xboole_0(B_77) | ~r2_hidden(A_78, A_79) | ~r1_tarski(A_79, B_77))), inference(resolution, [status(thm)], [c_18, c_255])).
% 7.58/2.62  tff(c_300, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r1_tarski(A_86, B_85) | k1_xboole_0=A_86)), inference(resolution, [status(thm)], [c_22, c_292])).
% 7.58/2.62  tff(c_321, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_6, c_300])).
% 7.58/2.62  tff(c_9484, plain, ('#skF_2'('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_9473, c_321])).
% 7.58/2.62  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.58/2.62  tff(c_157, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.58/2.62  tff(c_170, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_157])).
% 7.58/2.62  tff(c_1110, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | k4_xboole_0('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1107, c_170])).
% 7.58/2.62  tff(c_1124, plain, (k4_xboole_0('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1024, c_1110])).
% 7.58/2.62  tff(c_9491, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9484, c_1124])).
% 7.58/2.62  tff(c_9499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_9491])).
% 7.58/2.62  tff(c_9501, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 7.58/2.62  tff(c_9500, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 7.58/2.62  tff(c_9825, plain, (![B_376, A_377]: (v2_tex_2(B_376, A_377) | ~v3_tex_2(B_376, A_377) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.58/2.62  tff(c_9832, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_9825])).
% 7.58/2.62  tff(c_9836, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_9500, c_9832])).
% 7.58/2.62  tff(c_10284, plain, (![B_425, A_426]: (v1_zfmisc_1(B_425) | ~v2_tex_2(B_425, A_426) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_426))) | v1_xboole_0(B_425) | ~l1_pre_topc(A_426) | ~v2_tdlat_3(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.62  tff(c_10291, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_10284])).
% 7.58/2.62  tff(c_10295, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_9836, c_10291])).
% 7.58/2.62  tff(c_10297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_9501, c_10295])).
% 7.58/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/2.62  
% 7.58/2.62  Inference rules
% 7.58/2.62  ----------------------
% 7.58/2.62  #Ref     : 0
% 7.58/2.62  #Sup     : 2444
% 7.58/2.62  #Fact    : 6
% 7.58/2.62  #Define  : 0
% 7.58/2.62  #Split   : 25
% 7.58/2.62  #Chain   : 0
% 7.58/2.62  #Close   : 0
% 7.58/2.62  
% 7.58/2.62  Ordering : KBO
% 7.58/2.62  
% 7.58/2.62  Simplification rules
% 7.58/2.62  ----------------------
% 7.58/2.62  #Subsume      : 1377
% 7.58/2.62  #Demod        : 1320
% 7.58/2.62  #Tautology    : 585
% 7.58/2.62  #SimpNegUnit  : 504
% 7.58/2.62  #BackRed      : 9
% 7.58/2.62  
% 7.58/2.62  #Partial instantiations: 0
% 7.58/2.62  #Strategies tried      : 1
% 7.58/2.62  
% 7.58/2.62  Timing (in seconds)
% 7.58/2.62  ----------------------
% 7.58/2.62  Preprocessing        : 0.32
% 7.58/2.62  Parsing              : 0.18
% 7.58/2.62  CNF conversion       : 0.02
% 7.58/2.62  Main loop            : 1.44
% 7.58/2.62  Inferencing          : 0.46
% 7.58/2.62  Reduction            : 0.50
% 7.58/2.62  Demodulation         : 0.34
% 7.58/2.62  BG Simplification    : 0.04
% 7.58/2.62  Subsumption          : 0.36
% 7.58/2.62  Abstraction          : 0.08
% 7.58/2.62  MUC search           : 0.00
% 7.58/2.62  Cooper               : 0.00
% 7.58/2.62  Total                : 1.83
% 7.58/2.62  Index Insertion      : 0.00
% 7.58/2.62  Index Deletion       : 0.00
% 7.58/2.62  Index Matching       : 0.00
% 7.58/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
