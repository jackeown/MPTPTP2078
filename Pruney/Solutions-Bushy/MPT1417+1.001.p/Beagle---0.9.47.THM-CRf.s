%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1417+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:55 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 705 expanded)
%              Number of leaves         :   30 ( 269 expanded)
%              Depth                    :   15
%              Number of atoms          :  364 (2964 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r6_binop_1 > r5_binop_1 > r4_binop_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_eqrel_1,type,(
    k8_eqrel_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(r6_binop_1,type,(
    r6_binop_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r4_binop_1,type,(
    r4_binop_1: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k3_filter_1,type,(
    k3_filter_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(m2_filter_1,type,(
    m2_filter_1: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r5_binop_1,type,(
    r5_binop_1: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_partfun1(B,A)
              & v3_relat_2(B)
              & v8_relat_2(B)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( m2_filter_1(C,A,B)
               => ! [D] :
                    ( m2_filter_1(D,A,B)
                   => ( r6_binop_1(A,C,D)
                     => r6_binop_1(k8_eqrel_1(A,B),k3_filter_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_filter_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r6_binop_1(A,B,C)
          <=> ( r4_binop_1(A,B,C)
              & r5_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_binop_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( m2_filter_1(C,A,B)
             => ! [D] :
                  ( m2_filter_1(D,A,B)
                 => ( r5_binop_1(A,C,D)
                   => r5_binop_1(k8_eqrel_1(A,B),k3_filter_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_filter_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( m2_filter_1(C,A,B)
             => ! [D] :
                  ( m2_filter_1(D,A,B)
                 => ( r4_binop_1(A,C,D)
                   => r4_binop_1(k8_eqrel_1(A,B),k3_filter_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_filter_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_partfun1(B,A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ( v1_funct_1(k3_filter_1(A,B,C))
        & v1_funct_2(k3_filter_1(A,B,C),k2_zfmisc_1(k8_eqrel_1(A,B),k8_eqrel_1(A,B)),k8_eqrel_1(A,B))
        & m1_subset_1(k3_filter_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A,B),k8_eqrel_1(A,B)),k8_eqrel_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_40,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_38,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    m2_filter_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_30,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_43,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_47,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_48,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_funct_1(C_59)
      | ~ m2_filter_1(C_59,A_60,B_61)
      | ~ v1_relat_1(B_61)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,
    ( v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_61,plain,
    ( v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_54])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_61])).

tff(c_63,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_funct_2(C_62,k2_zfmisc_1(A_63,A_63),A_63)
      | ~ m2_filter_1(C_62,A_63,B_64)
      | ~ v1_relat_1(B_64)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_67,plain,
    ( v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_74,plain,
    ( v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_67])).

tff(c_75,plain,(
    v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_74])).

tff(c_76,plain,(
    ! [C_65,A_66,B_67] :
      ( m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_66,A_66),A_66)))
      | ~ m2_filter_1(C_65,A_66,B_67)
      | ~ v1_relat_1(B_67)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_87,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_80])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_87])).

tff(c_51,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_57,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_51])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_57])).

tff(c_65,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_63])).

tff(c_70,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_65])).

tff(c_71,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_70])).

tff(c_78,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_76])).

tff(c_83,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_78])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_83])).

tff(c_28,plain,(
    r6_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_126,plain,(
    ! [A_81,B_82,C_83] :
      ( r5_binop_1(A_81,B_82,C_83)
      | ~ r6_binop_1(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_81,A_81),A_81)))
      | ~ v1_funct_2(C_83,k2_zfmisc_1(A_81,A_81),A_81)
      | ~ v1_funct_1(C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_81,A_81),A_81)))
      | ~ v1_funct_2(B_82,k2_zfmisc_1(A_81,A_81),A_81)
      | ~ v1_funct_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,
    ( r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_131,plain,(
    r5_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_75,c_88,c_58,c_71,c_84,c_128])).

tff(c_22,plain,(
    ! [A_15,B_23,C_27,D_29] :
      ( r5_binop_1(k8_eqrel_1(A_15,B_23),k3_filter_1(A_15,B_23,C_27),k3_filter_1(A_15,B_23,D_29))
      | ~ r5_binop_1(A_15,C_27,D_29)
      | ~ m2_filter_1(D_29,A_15,B_23)
      | ~ m2_filter_1(C_27,A_15,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_15,A_15)))
      | ~ v8_relat_2(B_23)
      | ~ v3_relat_2(B_23)
      | ~ v1_partfun1(B_23,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_132,plain,(
    ! [A_84,B_85,C_86] :
      ( r4_binop_1(A_84,B_85,C_86)
      | ~ r6_binop_1(A_84,B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84,A_84),A_84)))
      | ~ v1_funct_2(C_86,k2_zfmisc_1(A_84,A_84),A_84)
      | ~ v1_funct_1(C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84,A_84),A_84)))
      | ~ v1_funct_2(B_85,k2_zfmisc_1(A_84,A_84),A_84)
      | ~ v1_funct_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,
    ( r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_137,plain,(
    r4_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_75,c_88,c_58,c_71,c_84,c_134])).

tff(c_24,plain,(
    ! [A_30,B_38,C_42,D_44] :
      ( r4_binop_1(k8_eqrel_1(A_30,B_38),k3_filter_1(A_30,B_38,C_42),k3_filter_1(A_30,B_38,D_44))
      | ~ r4_binop_1(A_30,C_42,D_44)
      | ~ m2_filter_1(D_44,A_30,B_38)
      | ~ m2_filter_1(C_42,A_30,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v8_relat_2(B_38)
      | ~ v3_relat_2(B_38)
      | ~ v1_partfun1(B_38,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_97,plain,(
    ! [A_68,B_69,C_70] :
      ( v1_funct_1(k3_filter_1(A_68,B_69,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_68,A_68),A_68)))
      | ~ v1_funct_2(C_70,k2_zfmisc_1(A_68,A_68),A_68)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_zfmisc_1(A_68,A_68)))
      | ~ v8_relat_2(B_69)
      | ~ v3_relat_2(B_69)
      | ~ v1_partfun1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_99,plain,(
    ! [B_69] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_69,'#skF_3'))
      | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_69)
      | ~ v3_relat_2(B_69)
      | ~ v1_partfun1(B_69,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_88,c_97])).

tff(c_104,plain,(
    ! [B_69] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_69,'#skF_3'))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_69)
      | ~ v3_relat_2(B_69)
      | ~ v1_partfun1(B_69,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_75,c_99])).

tff(c_110,plain,(
    ! [B_71] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_71,'#skF_3'))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_71)
      | ~ v3_relat_2(B_71)
      | ~ v1_partfun1(B_71,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_104])).

tff(c_113,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_3'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_116,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_113])).

tff(c_101,plain,(
    ! [B_69] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_69,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_69)
      | ~ v3_relat_2(B_69)
      | ~ v1_partfun1(B_69,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_97])).

tff(c_108,plain,(
    ! [B_69] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_69,'#skF_4'))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_69)
      | ~ v3_relat_2(B_69)
      | ~ v1_partfun1(B_69,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_71,c_101])).

tff(c_118,plain,(
    ! [B_76] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_76,'#skF_4'))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_76)
      | ~ v3_relat_2(B_76)
      | ~ v1_partfun1(B_76,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_108])).

tff(c_121,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_124,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_121])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( v1_funct_2(k3_filter_1(A_8,B_9,C_10),k2_zfmisc_1(k8_eqrel_1(A_8,B_9),k8_eqrel_1(A_8,B_9)),k8_eqrel_1(A_8,B_9))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_8,A_8),A_8)))
      | ~ v1_funct_2(C_10,k2_zfmisc_1(A_8,A_8),A_8)
      | ~ v1_funct_1(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_zfmisc_1(A_8,A_8)))
      | ~ v8_relat_2(B_9)
      | ~ v3_relat_2(B_9)
      | ~ v1_partfun1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k3_filter_1(A_8,B_9,C_10),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_8,B_9),k8_eqrel_1(A_8,B_9)),k8_eqrel_1(A_8,B_9))))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_8,A_8),A_8)))
      | ~ v1_funct_2(C_10,k2_zfmisc_1(A_8,A_8),A_8)
      | ~ v1_funct_1(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_zfmisc_1(A_8,A_8)))
      | ~ v8_relat_2(B_9)
      | ~ v3_relat_2(B_9)
      | ~ v1_partfun1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_179,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k3_filter_1(A_95,B_96,C_97),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_95,B_96),k8_eqrel_1(A_95,B_96)),k8_eqrel_1(A_95,B_96))))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_95,A_95),A_95)))
      | ~ v1_funct_2(C_97,k2_zfmisc_1(A_95,A_95),A_95)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v8_relat_2(B_96)
      | ~ v3_relat_2(B_96)
      | ~ v1_partfun1(B_96,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_4,B_5,C_7] :
      ( r6_binop_1(A_4,B_5,C_7)
      | ~ r5_binop_1(A_4,B_5,C_7)
      | ~ r4_binop_1(A_4,B_5,C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_4,A_4),A_4)))
      | ~ v1_funct_2(C_7,k2_zfmisc_1(A_4,A_4),A_4)
      | ~ v1_funct_1(C_7)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_4,A_4),A_4)))
      | ~ v1_funct_2(B_5,k2_zfmisc_1(A_4,A_4),A_4)
      | ~ v1_funct_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_230,plain,(
    ! [A_119,B_120,B_121,C_122] :
      ( r6_binop_1(k8_eqrel_1(A_119,B_120),B_121,k3_filter_1(A_119,B_120,C_122))
      | ~ r5_binop_1(k8_eqrel_1(A_119,B_120),B_121,k3_filter_1(A_119,B_120,C_122))
      | ~ r4_binop_1(k8_eqrel_1(A_119,B_120),B_121,k3_filter_1(A_119,B_120,C_122))
      | ~ v1_funct_2(k3_filter_1(A_119,B_120,C_122),k2_zfmisc_1(k8_eqrel_1(A_119,B_120),k8_eqrel_1(A_119,B_120)),k8_eqrel_1(A_119,B_120))
      | ~ v1_funct_1(k3_filter_1(A_119,B_120,C_122))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_119,B_120),k8_eqrel_1(A_119,B_120)),k8_eqrel_1(A_119,B_120))))
      | ~ v1_funct_2(B_121,k2_zfmisc_1(k8_eqrel_1(A_119,B_120),k8_eqrel_1(A_119,B_120)),k8_eqrel_1(A_119,B_120))
      | ~ v1_funct_1(B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_119,A_119),A_119)))
      | ~ v1_funct_2(C_122,k2_zfmisc_1(A_119,A_119),A_119)
      | ~ v1_funct_1(C_122)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v8_relat_2(B_120)
      | ~ v3_relat_2(B_120)
      | ~ v1_partfun1(B_120,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_179,c_4])).

tff(c_234,plain,(
    ! [A_123,B_124,B_125,C_126] :
      ( r6_binop_1(k8_eqrel_1(A_123,B_124),B_125,k3_filter_1(A_123,B_124,C_126))
      | ~ r5_binop_1(k8_eqrel_1(A_123,B_124),B_125,k3_filter_1(A_123,B_124,C_126))
      | ~ r4_binop_1(k8_eqrel_1(A_123,B_124),B_125,k3_filter_1(A_123,B_124,C_126))
      | ~ v1_funct_1(k3_filter_1(A_123,B_124,C_126))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_123,B_124),k8_eqrel_1(A_123,B_124)),k8_eqrel_1(A_123,B_124))))
      | ~ v1_funct_2(B_125,k2_zfmisc_1(k8_eqrel_1(A_123,B_124),k8_eqrel_1(A_123,B_124)),k8_eqrel_1(A_123,B_124))
      | ~ v1_funct_1(B_125)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_123,A_123),A_123)))
      | ~ v1_funct_2(C_126,k2_zfmisc_1(A_123,A_123),A_123)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1(A_123,A_123)))
      | ~ v8_relat_2(B_124)
      | ~ v3_relat_2(B_124)
      | ~ v1_partfun1(B_124,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_12,c_230])).

tff(c_238,plain,(
    ! [A_127,B_128,C_129,C_130] :
      ( r6_binop_1(k8_eqrel_1(A_127,B_128),k3_filter_1(A_127,B_128,C_129),k3_filter_1(A_127,B_128,C_130))
      | ~ r5_binop_1(k8_eqrel_1(A_127,B_128),k3_filter_1(A_127,B_128,C_129),k3_filter_1(A_127,B_128,C_130))
      | ~ r4_binop_1(k8_eqrel_1(A_127,B_128),k3_filter_1(A_127,B_128,C_129),k3_filter_1(A_127,B_128,C_130))
      | ~ v1_funct_1(k3_filter_1(A_127,B_128,C_130))
      | ~ v1_funct_2(k3_filter_1(A_127,B_128,C_129),k2_zfmisc_1(k8_eqrel_1(A_127,B_128),k8_eqrel_1(A_127,B_128)),k8_eqrel_1(A_127,B_128))
      | ~ v1_funct_1(k3_filter_1(A_127,B_128,C_129))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_127,A_127),A_127)))
      | ~ v1_funct_2(C_130,k2_zfmisc_1(A_127,A_127),A_127)
      | ~ v1_funct_1(C_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_127,A_127),A_127)))
      | ~ v1_funct_2(C_129,k2_zfmisc_1(A_127,A_127),A_127)
      | ~ v1_funct_1(C_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_zfmisc_1(A_127,A_127)))
      | ~ v8_relat_2(B_128)
      | ~ v3_relat_2(B_128)
      | ~ v1_partfun1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_10,c_234])).

tff(c_242,plain,(
    ! [A_131,B_132,C_133,C_134] :
      ( r6_binop_1(k8_eqrel_1(A_131,B_132),k3_filter_1(A_131,B_132,C_133),k3_filter_1(A_131,B_132,C_134))
      | ~ r5_binop_1(k8_eqrel_1(A_131,B_132),k3_filter_1(A_131,B_132,C_133),k3_filter_1(A_131,B_132,C_134))
      | ~ r4_binop_1(k8_eqrel_1(A_131,B_132),k3_filter_1(A_131,B_132,C_133),k3_filter_1(A_131,B_132,C_134))
      | ~ v1_funct_1(k3_filter_1(A_131,B_132,C_134))
      | ~ v1_funct_1(k3_filter_1(A_131,B_132,C_133))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_131,A_131),A_131)))
      | ~ v1_funct_2(C_134,k2_zfmisc_1(A_131,A_131),A_131)
      | ~ v1_funct_1(C_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_131,A_131),A_131)))
      | ~ v1_funct_2(C_133,k2_zfmisc_1(A_131,A_131),A_131)
      | ~ v1_funct_1(C_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_zfmisc_1(A_131,A_131)))
      | ~ v8_relat_2(B_132)
      | ~ v3_relat_2(B_132)
      | ~ v1_partfun1(B_132,A_131)
      | v1_xboole_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_12,c_238])).

tff(c_26,plain,(
    ~ r6_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_249,plain,
    ( ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_26])).

tff(c_254,plain,
    ( ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_62,c_75,c_88,c_58,c_71,c_84,c_116,c_124,c_249])).

tff(c_255,plain,
    ( ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_254])).

tff(c_256,plain,(
    ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_259,plain,
    ( ~ r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m2_filter_1('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_262,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_30,c_137,c_259])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_262])).

tff(c_265,plain,(
    ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_269,plain,
    ( ~ r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m2_filter_1('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_265])).

tff(c_272,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_30,c_131,c_269])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_272])).

%------------------------------------------------------------------------------
