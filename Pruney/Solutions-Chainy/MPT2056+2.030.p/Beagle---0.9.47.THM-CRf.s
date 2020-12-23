%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 6.18s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 294 expanded)
%              Number of leaves         :   46 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 ( 736 expanded)
%              Number of equality atoms :   41 ( 170 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_81,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_97,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_75,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_120,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_124,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_129,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(u1_struct_0(A_50))
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_132,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_129])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_132])).

tff(c_138,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_137])).

tff(c_42,plain,(
    ! [A_26] : k9_setfam_1(A_26) = k1_zfmisc_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [A_30] : u1_struct_0(k3_yellow_1(A_30)) = k9_setfam_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_71,plain,(
    v1_subset_1('#skF_6',k9_setfam_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_76,plain,(
    v1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_71])).

tff(c_62,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_632,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_2'(A_132,B_133,C_134),A_132)
      | r2_hidden('#skF_3'(A_132,B_133,C_134),C_134)
      | k4_xboole_0(A_132,B_133) = C_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_988,plain,(
    ! [A_156,C_157] :
      ( r2_hidden('#skF_3'(A_156,A_156,C_157),C_157)
      | k4_xboole_0(A_156,A_156) = C_157 ) ),
    inference(resolution,[status(thm)],[c_632,c_20])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_249,plain,(
    ! [D_80,B_81,A_82] :
      ( ~ r2_hidden(D_80,B_81)
      | ~ r2_hidden(D_80,k4_xboole_0(A_82,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_268,plain,(
    ! [D_83,A_84] :
      ( ~ r2_hidden(D_83,A_84)
      | ~ r2_hidden(D_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_249])).

tff(c_347,plain,(
    ! [A_95,B_96] :
      ( ~ r2_hidden('#skF_4'(A_95,B_96),k1_xboole_0)
      | r1_xboole_0(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_26,c_268])).

tff(c_358,plain,(
    ! [A_97] : r1_xboole_0(A_97,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_347])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden(A_19,B_20)
      | ~ r1_xboole_0(k1_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_369,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_358,c_36])).

tff(c_1025,plain,(
    ! [A_156] : k4_xboole_0(A_156,A_156) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_988,c_369])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_278,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,B_86)
      | ~ r2_hidden(C_87,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_957,plain,(
    ! [C_153,B_154,A_155] :
      ( ~ r2_hidden(C_153,B_154)
      | ~ r2_hidden(C_153,A_155)
      | k4_xboole_0(A_155,B_154) != A_155 ) ),
    inference(resolution,[status(thm)],[c_34,c_278])).

tff(c_2077,plain,(
    ! [A_212,A_213] :
      ( ~ r2_hidden('#skF_1'(A_212),A_213)
      | k4_xboole_0(A_213,A_212) != A_213
      | v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_4,c_957])).

tff(c_2096,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_2077])).

tff(c_2162,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_2096])).

tff(c_329,plain,(
    ! [A_90,B_91,C_92] :
      ( k7_subset_1(A_90,B_91,C_92) = k4_xboole_0(B_91,C_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_332,plain,(
    ! [C_92] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_5')),'#skF_6',C_92) = k4_xboole_0('#skF_6',C_92) ),
    inference(resolution,[status(thm)],[c_77,c_329])).

tff(c_52,plain,(
    ! [A_31,B_33] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))),B_33,k1_tarski(k1_xboole_0)) = k2_yellow19(A_31,k3_yellow19(A_31,k2_struct_0(A_31),B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31)))))
      | ~ v13_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | ~ v2_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | v1_xboole_0(B_33)
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_74,plain,(
    ! [A_31,B_33] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_31)),B_33,k1_tarski(k1_xboole_0)) = k2_yellow19(A_31,k3_yellow19(A_31,k2_struct_0(A_31),B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_31))))
      | ~ v13_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | ~ v2_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | v1_xboole_0(B_33)
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_52])).

tff(c_1576,plain,(
    ! [A_193,B_194] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_193)),B_194,k1_tarski(k1_xboole_0)) = k2_yellow19(A_193,k3_yellow19(A_193,k2_struct_0(A_193),B_194))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_193))))
      | ~ v13_waybel_0(B_194,k3_yellow_1(k2_struct_0(A_193)))
      | ~ v2_waybel_0(B_194,k3_yellow_1(k2_struct_0(A_193)))
      | v1_xboole_0(B_194)
      | ~ l1_struct_0(A_193)
      | v2_struct_0(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_74])).

tff(c_1578,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_5')),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_77,c_1576])).

tff(c_1581,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_60,c_332,c_1578])).

tff(c_1582,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_1581])).

tff(c_56,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1751,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_56])).

tff(c_212,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_4'(A_73,B_74),B_74)
      | r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),k1_tarski(B_22))
      | B_22 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_150,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ r1_xboole_0(k1_tarski(A_57),B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_159,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden(A_21,k1_tarski(B_22))
      | B_22 = A_21 ) ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_498,plain,(
    ! [A_115,B_116] :
      ( '#skF_4'(A_115,k1_tarski(B_116)) = B_116
      | r1_xboole_0(A_115,k1_tarski(B_116)) ) ),
    inference(resolution,[status(thm)],[c_212,c_159])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7777,plain,(
    ! [A_388,B_389] :
      ( k4_xboole_0(A_388,k1_tarski(B_389)) = A_388
      | '#skF_4'(A_388,k1_tarski(B_389)) = B_389 ) ),
    inference(resolution,[status(thm)],[c_498,c_32])).

tff(c_8133,plain,(
    '#skF_4'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7777,c_1751])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8155,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8133,c_28])).

tff(c_8160,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8155])).

tff(c_8165,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8160,c_32])).

tff(c_8170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1751,c_8165])).

tff(c_8171,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_8155])).

tff(c_54,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34))))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,u1_struct_0(k3_yellow_1(A_34)))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_73,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k9_setfam_1(A_34)))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,k9_setfam_1(A_34))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_54])).

tff(c_78,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,k1_zfmisc_1(A_34))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_73])).

tff(c_8182,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_6',k1_zfmisc_1(A_34))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_8171,c_78])).

tff(c_8198,plain,(
    ! [A_34] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_6',k1_zfmisc_1(A_34))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2162,c_8182])).

tff(c_8545,plain,(
    ! [A_395] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(A_395)))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_395))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_395))
      | ~ v1_subset_1('#skF_6',k1_zfmisc_1(A_395))
      | v1_xboole_0(A_395) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_8198])).

tff(c_8548,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_77,c_8545])).

tff(c_8551,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62,c_60,c_8548])).

tff(c_8553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_8551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:33:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.18/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.18/2.29  
% 6.18/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.18/2.29  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.18/2.29  
% 6.18/2.29  %Foreground sorts:
% 6.18/2.29  
% 6.18/2.29  
% 6.18/2.29  %Background operators:
% 6.18/2.29  
% 6.18/2.29  
% 6.18/2.29  %Foreground operators:
% 6.18/2.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.18/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.18/2.29  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 6.18/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.18/2.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.18/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.18/2.29  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 6.18/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.18/2.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.18/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.18/2.29  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 6.18/2.29  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 6.18/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.18/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.18/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.18/2.29  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.18/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.18/2.29  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 6.18/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.18/2.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.18/2.29  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 6.18/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.18/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.18/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.18/2.29  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 6.18/2.29  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 6.18/2.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.18/2.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.18/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.18/2.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.18/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.18/2.29  
% 6.40/2.31  tff(f_155, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 6.40/2.31  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.40/2.31  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.40/2.31  tff(f_81, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 6.40/2.31  tff(f_97, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_7)).
% 6.40/2.31  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.40/2.31  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.40/2.31  tff(f_61, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.40/2.31  tff(f_70, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 6.40/2.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.40/2.31  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.40/2.31  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.40/2.31  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 6.40/2.31  tff(f_75, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 6.40/2.31  tff(f_135, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 6.40/2.31  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_68, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_120, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.40/2.31  tff(c_124, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_120])).
% 6.40/2.31  tff(c_129, plain, (![A_50]: (~v1_xboole_0(u1_struct_0(A_50)) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.40/2.31  tff(c_132, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_124, c_129])).
% 6.40/2.31  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_132])).
% 6.40/2.31  tff(c_138, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_137])).
% 6.40/2.31  tff(c_42, plain, (![A_26]: (k9_setfam_1(A_26)=k1_zfmisc_1(A_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.40/2.31  tff(c_50, plain, (![A_30]: (u1_struct_0(k3_yellow_1(A_30))=k9_setfam_1(A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.40/2.31  tff(c_64, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_71, plain, (v1_subset_1('#skF_6', k9_setfam_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64])).
% 6.40/2.31  tff(c_76, plain, (v1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_71])).
% 6.40/2.31  tff(c_62, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_60, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_58])).
% 6.40/2.31  tff(c_77, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72])).
% 6.40/2.31  tff(c_66, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_632, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_2'(A_132, B_133, C_134), A_132) | r2_hidden('#skF_3'(A_132, B_133, C_134), C_134) | k4_xboole_0(A_132, B_133)=C_134)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.40/2.31  tff(c_20, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.40/2.31  tff(c_988, plain, (![A_156, C_157]: (r2_hidden('#skF_3'(A_156, A_156, C_157), C_157) | k4_xboole_0(A_156, A_156)=C_157)), inference(resolution, [status(thm)], [c_632, c_20])).
% 6.40/2.31  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.40/2.31  tff(c_30, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.40/2.31  tff(c_249, plain, (![D_80, B_81, A_82]: (~r2_hidden(D_80, B_81) | ~r2_hidden(D_80, k4_xboole_0(A_82, B_81)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.40/2.31  tff(c_268, plain, (![D_83, A_84]: (~r2_hidden(D_83, A_84) | ~r2_hidden(D_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_249])).
% 6.40/2.31  tff(c_347, plain, (![A_95, B_96]: (~r2_hidden('#skF_4'(A_95, B_96), k1_xboole_0) | r1_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_26, c_268])).
% 6.40/2.31  tff(c_358, plain, (![A_97]: (r1_xboole_0(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_347])).
% 6.40/2.31  tff(c_36, plain, (![A_19, B_20]: (~r2_hidden(A_19, B_20) | ~r1_xboole_0(k1_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.40/2.31  tff(c_369, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_358, c_36])).
% 6.40/2.31  tff(c_1025, plain, (![A_156]: (k4_xboole_0(A_156, A_156)=k1_xboole_0)), inference(resolution, [status(thm)], [c_988, c_369])).
% 6.40/2.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.40/2.31  tff(c_34, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.40/2.31  tff(c_278, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, B_86) | ~r2_hidden(C_87, A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.40/2.31  tff(c_957, plain, (![C_153, B_154, A_155]: (~r2_hidden(C_153, B_154) | ~r2_hidden(C_153, A_155) | k4_xboole_0(A_155, B_154)!=A_155)), inference(resolution, [status(thm)], [c_34, c_278])).
% 6.40/2.31  tff(c_2077, plain, (![A_212, A_213]: (~r2_hidden('#skF_1'(A_212), A_213) | k4_xboole_0(A_213, A_212)!=A_213 | v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_4, c_957])).
% 6.40/2.31  tff(c_2096, plain, (![A_1]: (k4_xboole_0(A_1, A_1)!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_2077])).
% 6.40/2.31  tff(c_2162, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1025, c_2096])).
% 6.40/2.31  tff(c_329, plain, (![A_90, B_91, C_92]: (k7_subset_1(A_90, B_91, C_92)=k4_xboole_0(B_91, C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.40/2.31  tff(c_332, plain, (![C_92]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_5')), '#skF_6', C_92)=k4_xboole_0('#skF_6', C_92))), inference(resolution, [status(thm)], [c_77, c_329])).
% 6.40/2.31  tff(c_52, plain, (![A_31, B_33]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))), B_33, k1_tarski(k1_xboole_0))=k2_yellow19(A_31, k3_yellow19(A_31, k2_struct_0(A_31), B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))))) | ~v13_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | ~v2_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | v1_xboole_0(B_33) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.40/2.31  tff(c_74, plain, (![A_31, B_33]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_31)), B_33, k1_tarski(k1_xboole_0))=k2_yellow19(A_31, k3_yellow19(A_31, k2_struct_0(A_31), B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_31)))) | ~v13_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | ~v2_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | v1_xboole_0(B_33) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_52])).
% 6.40/2.31  tff(c_1576, plain, (![A_193, B_194]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_193)), B_194, k1_tarski(k1_xboole_0))=k2_yellow19(A_193, k3_yellow19(A_193, k2_struct_0(A_193), B_194)) | ~m1_subset_1(B_194, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_193)))) | ~v13_waybel_0(B_194, k3_yellow_1(k2_struct_0(A_193))) | ~v2_waybel_0(B_194, k3_yellow_1(k2_struct_0(A_193))) | v1_xboole_0(B_194) | ~l1_struct_0(A_193) | v2_struct_0(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_74])).
% 6.40/2.31  tff(c_1578, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_5')), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_77, c_1576])).
% 6.40/2.31  tff(c_1581, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_60, c_332, c_1578])).
% 6.40/2.31  tff(c_1582, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_1581])).
% 6.40/2.31  tff(c_56, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.40/2.31  tff(c_1751, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_56])).
% 6.40/2.31  tff(c_212, plain, (![A_73, B_74]: (r2_hidden('#skF_4'(A_73, B_74), B_74) | r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.40/2.31  tff(c_38, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), k1_tarski(B_22)) | B_22=A_21)), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.40/2.31  tff(c_150, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~r1_xboole_0(k1_tarski(A_57), B_58))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.40/2.31  tff(c_159, plain, (![A_21, B_22]: (~r2_hidden(A_21, k1_tarski(B_22)) | B_22=A_21)), inference(resolution, [status(thm)], [c_38, c_150])).
% 6.40/2.31  tff(c_498, plain, (![A_115, B_116]: ('#skF_4'(A_115, k1_tarski(B_116))=B_116 | r1_xboole_0(A_115, k1_tarski(B_116)))), inference(resolution, [status(thm)], [c_212, c_159])).
% 6.40/2.31  tff(c_32, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.40/2.31  tff(c_7777, plain, (![A_388, B_389]: (k4_xboole_0(A_388, k1_tarski(B_389))=A_388 | '#skF_4'(A_388, k1_tarski(B_389))=B_389)), inference(resolution, [status(thm)], [c_498, c_32])).
% 6.40/2.31  tff(c_8133, plain, ('#skF_4'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7777, c_1751])).
% 6.40/2.31  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.40/2.31  tff(c_8155, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8133, c_28])).
% 6.40/2.31  tff(c_8160, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8155])).
% 6.40/2.31  tff(c_8165, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(resolution, [status(thm)], [c_8160, c_32])).
% 6.40/2.31  tff(c_8170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1751, c_8165])).
% 6.40/2.31  tff(c_8171, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_8155])).
% 6.40/2.31  tff(c_54, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34)))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, u1_struct_0(k3_yellow_1(A_34))) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.40/2.31  tff(c_73, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k9_setfam_1(A_34))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, k9_setfam_1(A_34)) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_54])).
% 6.40/2.31  tff(c_78, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_34))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, k1_zfmisc_1(A_34)) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_73])).
% 6.40/2.31  tff(c_8182, plain, (![A_34]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(A_34))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_6', k1_zfmisc_1(A_34)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_8171, c_78])).
% 6.40/2.31  tff(c_8198, plain, (![A_34]: (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(A_34))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_6', k1_zfmisc_1(A_34)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_2162, c_8182])).
% 6.40/2.31  tff(c_8545, plain, (![A_395]: (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(A_395))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_395)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_395)) | ~v1_subset_1('#skF_6', k1_zfmisc_1(A_395)) | v1_xboole_0(A_395))), inference(negUnitSimplification, [status(thm)], [c_66, c_8198])).
% 6.40/2.31  tff(c_8548, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5'))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_77, c_8545])).
% 6.40/2.31  tff(c_8551, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62, c_60, c_8548])).
% 6.40/2.31  tff(c_8553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_8551])).
% 6.40/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.40/2.31  
% 6.40/2.31  Inference rules
% 6.40/2.31  ----------------------
% 6.40/2.31  #Ref     : 1
% 6.40/2.31  #Sup     : 2165
% 6.40/2.31  #Fact    : 0
% 6.40/2.31  #Define  : 0
% 6.40/2.31  #Split   : 2
% 6.40/2.31  #Chain   : 0
% 6.40/2.31  #Close   : 0
% 6.40/2.31  
% 6.40/2.31  Ordering : KBO
% 6.40/2.31  
% 6.40/2.31  Simplification rules
% 6.40/2.31  ----------------------
% 6.40/2.31  #Subsume      : 781
% 6.40/2.31  #Demod        : 685
% 6.40/2.31  #Tautology    : 708
% 6.40/2.31  #SimpNegUnit  : 23
% 6.40/2.31  #BackRed      : 2
% 6.40/2.31  
% 6.40/2.31  #Partial instantiations: 0
% 6.40/2.31  #Strategies tried      : 1
% 6.40/2.31  
% 6.40/2.31  Timing (in seconds)
% 6.40/2.31  ----------------------
% 6.40/2.31  Preprocessing        : 0.35
% 6.40/2.31  Parsing              : 0.18
% 6.40/2.31  CNF conversion       : 0.02
% 6.40/2.31  Main loop            : 1.19
% 6.40/2.31  Inferencing          : 0.40
% 6.40/2.31  Reduction            : 0.38
% 6.40/2.31  Demodulation         : 0.26
% 6.40/2.31  BG Simplification    : 0.05
% 6.40/2.31  Subsumption          : 0.28
% 6.40/2.31  Abstraction          : 0.07
% 6.40/2.31  MUC search           : 0.00
% 6.40/2.31  Cooper               : 0.00
% 6.40/2.31  Total                : 1.57
% 6.40/2.31  Index Insertion      : 0.00
% 6.40/2.31  Index Deletion       : 0.00
% 6.40/2.31  Index Matching       : 0.00
% 6.40/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
