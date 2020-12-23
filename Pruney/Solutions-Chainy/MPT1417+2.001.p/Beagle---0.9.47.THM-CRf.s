%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:36 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
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

tff(f_152,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_filter_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_48,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_binop_1)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_filter_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_filter_1)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_38,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_32,plain,(
    m2_filter_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_43,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_48,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_funct_1(C_59)
      | ~ m2_filter_1(C_59,A_60,B_61)
      | ~ v1_relat_1(B_61)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

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
    inference(cnfTransformation,[status(thm)],[f_85])).

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
    inference(cnfTransformation,[status(thm)],[f_85])).

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
    inference(cnfTransformation,[status(thm)],[f_152])).

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
    inference(cnfTransformation,[status(thm)],[f_48])).

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
    inference(cnfTransformation,[status(thm)],[f_107])).

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
    inference(cnfTransformation,[status(thm)],[f_48])).

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
    inference(cnfTransformation,[status(thm)],[f_129])).

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
    inference(cnfTransformation,[status(thm)],[f_71])).

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
    inference(cnfTransformation,[status(thm)],[f_71])).

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
    inference(cnfTransformation,[status(thm)],[f_71])).

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
    inference(cnfTransformation,[status(thm)],[f_71])).

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
    inference(cnfTransformation,[status(thm)],[f_48])).

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
    inference(cnfTransformation,[status(thm)],[f_152])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  %$ v1_funct_2 > r6_binop_1 > r5_binop_1 > r4_binop_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.43  
% 2.79/1.43  %Foreground sorts:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Background operators:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Foreground operators:
% 2.79/1.43  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 2.79/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.43  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.79/1.43  tff(r6_binop_1, type, r6_binop_1: ($i * $i * $i) > $o).
% 2.79/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.79/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.43  tff(r4_binop_1, type, r4_binop_1: ($i * $i * $i) > $o).
% 2.79/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.43  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.43  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 2.79/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.43  tff(r5_binop_1, type, r5_binop_1: ($i * $i * $i) > $o).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.43  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 2.79/1.43  
% 2.79/1.45  tff(f_152, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m2_filter_1(C, A, B) => (![D]: (m2_filter_1(D, A, B) => (r6_binop_1(A, C, D) => r6_binop_1(k8_eqrel_1(A, B), k3_filter_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_filter_1)).
% 2.79/1.45  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.45  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 2.79/1.45  tff(f_48, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, k2_zfmisc_1(A, A), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r6_binop_1(A, B, C) <=> (r4_binop_1(A, B, C) & r5_binop_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_binop_1)).
% 2.79/1.45  tff(f_107, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m2_filter_1(C, A, B) => (![D]: (m2_filter_1(D, A, B) => (r5_binop_1(A, C, D) => r5_binop_1(k8_eqrel_1(A, B), k3_filter_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_filter_1)).
% 2.79/1.45  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m2_filter_1(C, A, B) => (![D]: (m2_filter_1(D, A, B) => (r4_binop_1(A, C, D) => r4_binop_1(k8_eqrel_1(A, B), k3_filter_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_filter_1)).
% 2.79/1.45  tff(f_71, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 2.79/1.45  tff(c_42, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_40, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_38, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_36, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_32, plain, (m2_filter_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_30, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_43, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.45  tff(c_47, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_43])).
% 2.79/1.45  tff(c_48, plain, (![C_59, A_60, B_61]: (v1_funct_1(C_59) | ~m2_filter_1(C_59, A_60, B_61) | ~v1_relat_1(B_61) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_54, plain, (v1_funct_1('#skF_3') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.79/1.45  tff(c_61, plain, (v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_54])).
% 2.79/1.45  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_61])).
% 2.79/1.45  tff(c_63, plain, (![C_62, A_63, B_64]: (v1_funct_2(C_62, k2_zfmisc_1(A_63, A_63), A_63) | ~m2_filter_1(C_62, A_63, B_64) | ~v1_relat_1(B_64) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_67, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.79/1.45  tff(c_74, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_67])).
% 2.79/1.45  tff(c_75, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_74])).
% 2.79/1.45  tff(c_76, plain, (![C_65, A_66, B_67]: (m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_66, A_66), A_66))) | ~m2_filter_1(C_65, A_66, B_67) | ~v1_relat_1(B_67) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_76])).
% 2.79/1.45  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_80])).
% 2.79/1.45  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_42, c_87])).
% 2.79/1.45  tff(c_51, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_48])).
% 2.79/1.45  tff(c_57, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_51])).
% 2.79/1.45  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_57])).
% 2.79/1.45  tff(c_65, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_63])).
% 2.79/1.45  tff(c_70, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_65])).
% 2.79/1.45  tff(c_71, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_70])).
% 2.79/1.45  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_76])).
% 2.79/1.45  tff(c_83, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_78])).
% 2.79/1.45  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_42, c_83])).
% 2.79/1.45  tff(c_28, plain, (r6_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.45  tff(c_126, plain, (![A_81, B_82, C_83]: (r5_binop_1(A_81, B_82, C_83) | ~r6_binop_1(A_81, B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_81, A_81), A_81))) | ~v1_funct_2(C_83, k2_zfmisc_1(A_81, A_81), A_81) | ~v1_funct_1(C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_81, A_81), A_81))) | ~v1_funct_2(B_82, k2_zfmisc_1(A_81, A_81), A_81) | ~v1_funct_1(B_82))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.45  tff(c_128, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_126])).
% 2.79/1.45  tff(c_131, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_75, c_88, c_58, c_71, c_84, c_128])).
% 2.79/1.45  tff(c_22, plain, (![A_15, B_23, C_27, D_29]: (r5_binop_1(k8_eqrel_1(A_15, B_23), k3_filter_1(A_15, B_23, C_27), k3_filter_1(A_15, B_23, D_29)) | ~r5_binop_1(A_15, C_27, D_29) | ~m2_filter_1(D_29, A_15, B_23) | ~m2_filter_1(C_27, A_15, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))) | ~v8_relat_2(B_23) | ~v3_relat_2(B_23) | ~v1_partfun1(B_23, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.45  tff(c_132, plain, (![A_84, B_85, C_86]: (r4_binop_1(A_84, B_85, C_86) | ~r6_binop_1(A_84, B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84, A_84), A_84))) | ~v1_funct_2(C_86, k2_zfmisc_1(A_84, A_84), A_84) | ~v1_funct_1(C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84, A_84), A_84))) | ~v1_funct_2(B_85, k2_zfmisc_1(A_84, A_84), A_84) | ~v1_funct_1(B_85))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.45  tff(c_134, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_132])).
% 2.79/1.45  tff(c_137, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_75, c_88, c_58, c_71, c_84, c_134])).
% 2.79/1.45  tff(c_24, plain, (![A_30, B_38, C_42, D_44]: (r4_binop_1(k8_eqrel_1(A_30, B_38), k3_filter_1(A_30, B_38, C_42), k3_filter_1(A_30, B_38, D_44)) | ~r4_binop_1(A_30, C_42, D_44) | ~m2_filter_1(D_44, A_30, B_38) | ~m2_filter_1(C_42, A_30, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v8_relat_2(B_38) | ~v3_relat_2(B_38) | ~v1_partfun1(B_38, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.79/1.45  tff(c_97, plain, (![A_68, B_69, C_70]: (v1_funct_1(k3_filter_1(A_68, B_69, C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_68, A_68), A_68))) | ~v1_funct_2(C_70, k2_zfmisc_1(A_68, A_68), A_68) | ~v1_funct_1(C_70) | ~m1_subset_1(B_69, k1_zfmisc_1(k2_zfmisc_1(A_68, A_68))) | ~v8_relat_2(B_69) | ~v3_relat_2(B_69) | ~v1_partfun1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.45  tff(c_99, plain, (![B_69]: (v1_funct_1(k3_filter_1('#skF_1', B_69, '#skF_3')) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_69) | ~v3_relat_2(B_69) | ~v1_partfun1(B_69, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_97])).
% 2.79/1.46  tff(c_104, plain, (![B_69]: (v1_funct_1(k3_filter_1('#skF_1', B_69, '#skF_3')) | ~m1_subset_1(B_69, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_69) | ~v3_relat_2(B_69) | ~v1_partfun1(B_69, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_75, c_99])).
% 2.79/1.46  tff(c_110, plain, (![B_71]: (v1_funct_1(k3_filter_1('#skF_1', B_71, '#skF_3')) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_71) | ~v3_relat_2(B_71) | ~v1_partfun1(B_71, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_104])).
% 2.79/1.46  tff(c_113, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_3')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_110])).
% 2.79/1.46  tff(c_116, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_113])).
% 2.79/1.46  tff(c_101, plain, (![B_69]: (v1_funct_1(k3_filter_1('#skF_1', B_69, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_69) | ~v3_relat_2(B_69) | ~v1_partfun1(B_69, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_97])).
% 2.79/1.46  tff(c_108, plain, (![B_69]: (v1_funct_1(k3_filter_1('#skF_1', B_69, '#skF_4')) | ~m1_subset_1(B_69, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_69) | ~v3_relat_2(B_69) | ~v1_partfun1(B_69, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_71, c_101])).
% 2.79/1.46  tff(c_118, plain, (![B_76]: (v1_funct_1(k3_filter_1('#skF_1', B_76, '#skF_4')) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_76) | ~v3_relat_2(B_76) | ~v1_partfun1(B_76, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_108])).
% 2.79/1.46  tff(c_121, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.79/1.46  tff(c_124, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_121])).
% 2.79/1.46  tff(c_12, plain, (![A_8, B_9, C_10]: (v1_funct_2(k3_filter_1(A_8, B_9, C_10), k2_zfmisc_1(k8_eqrel_1(A_8, B_9), k8_eqrel_1(A_8, B_9)), k8_eqrel_1(A_8, B_9)) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_8, A_8), A_8))) | ~v1_funct_2(C_10, k2_zfmisc_1(A_8, A_8), A_8) | ~v1_funct_1(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))) | ~v8_relat_2(B_9) | ~v3_relat_2(B_9) | ~v1_partfun1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.46  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k3_filter_1(A_8, B_9, C_10), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_8, B_9), k8_eqrel_1(A_8, B_9)), k8_eqrel_1(A_8, B_9)))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_8, A_8), A_8))) | ~v1_funct_2(C_10, k2_zfmisc_1(A_8, A_8), A_8) | ~v1_funct_1(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))) | ~v8_relat_2(B_9) | ~v3_relat_2(B_9) | ~v1_partfun1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.46  tff(c_179, plain, (![A_95, B_96, C_97]: (m1_subset_1(k3_filter_1(A_95, B_96, C_97), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_95, B_96), k8_eqrel_1(A_95, B_96)), k8_eqrel_1(A_95, B_96)))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_95, A_95), A_95))) | ~v1_funct_2(C_97, k2_zfmisc_1(A_95, A_95), A_95) | ~v1_funct_1(C_97) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v8_relat_2(B_96) | ~v3_relat_2(B_96) | ~v1_partfun1(B_96, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.46  tff(c_4, plain, (![A_4, B_5, C_7]: (r6_binop_1(A_4, B_5, C_7) | ~r5_binop_1(A_4, B_5, C_7) | ~r4_binop_1(A_4, B_5, C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_4, A_4), A_4))) | ~v1_funct_2(C_7, k2_zfmisc_1(A_4, A_4), A_4) | ~v1_funct_1(C_7) | ~m1_subset_1(B_5, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_4, A_4), A_4))) | ~v1_funct_2(B_5, k2_zfmisc_1(A_4, A_4), A_4) | ~v1_funct_1(B_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.46  tff(c_230, plain, (![A_119, B_120, B_121, C_122]: (r6_binop_1(k8_eqrel_1(A_119, B_120), B_121, k3_filter_1(A_119, B_120, C_122)) | ~r5_binop_1(k8_eqrel_1(A_119, B_120), B_121, k3_filter_1(A_119, B_120, C_122)) | ~r4_binop_1(k8_eqrel_1(A_119, B_120), B_121, k3_filter_1(A_119, B_120, C_122)) | ~v1_funct_2(k3_filter_1(A_119, B_120, C_122), k2_zfmisc_1(k8_eqrel_1(A_119, B_120), k8_eqrel_1(A_119, B_120)), k8_eqrel_1(A_119, B_120)) | ~v1_funct_1(k3_filter_1(A_119, B_120, C_122)) | ~m1_subset_1(B_121, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_119, B_120), k8_eqrel_1(A_119, B_120)), k8_eqrel_1(A_119, B_120)))) | ~v1_funct_2(B_121, k2_zfmisc_1(k8_eqrel_1(A_119, B_120), k8_eqrel_1(A_119, B_120)), k8_eqrel_1(A_119, B_120)) | ~v1_funct_1(B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_119, A_119), A_119))) | ~v1_funct_2(C_122, k2_zfmisc_1(A_119, A_119), A_119) | ~v1_funct_1(C_122) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v8_relat_2(B_120) | ~v3_relat_2(B_120) | ~v1_partfun1(B_120, A_119) | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_179, c_4])).
% 2.79/1.46  tff(c_234, plain, (![A_123, B_124, B_125, C_126]: (r6_binop_1(k8_eqrel_1(A_123, B_124), B_125, k3_filter_1(A_123, B_124, C_126)) | ~r5_binop_1(k8_eqrel_1(A_123, B_124), B_125, k3_filter_1(A_123, B_124, C_126)) | ~r4_binop_1(k8_eqrel_1(A_123, B_124), B_125, k3_filter_1(A_123, B_124, C_126)) | ~v1_funct_1(k3_filter_1(A_123, B_124, C_126)) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_123, B_124), k8_eqrel_1(A_123, B_124)), k8_eqrel_1(A_123, B_124)))) | ~v1_funct_2(B_125, k2_zfmisc_1(k8_eqrel_1(A_123, B_124), k8_eqrel_1(A_123, B_124)), k8_eqrel_1(A_123, B_124)) | ~v1_funct_1(B_125) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_123, A_123), A_123))) | ~v1_funct_2(C_126, k2_zfmisc_1(A_123, A_123), A_123) | ~v1_funct_1(C_126) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1(A_123, A_123))) | ~v8_relat_2(B_124) | ~v3_relat_2(B_124) | ~v1_partfun1(B_124, A_123) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_12, c_230])).
% 2.79/1.46  tff(c_238, plain, (![A_127, B_128, C_129, C_130]: (r6_binop_1(k8_eqrel_1(A_127, B_128), k3_filter_1(A_127, B_128, C_129), k3_filter_1(A_127, B_128, C_130)) | ~r5_binop_1(k8_eqrel_1(A_127, B_128), k3_filter_1(A_127, B_128, C_129), k3_filter_1(A_127, B_128, C_130)) | ~r4_binop_1(k8_eqrel_1(A_127, B_128), k3_filter_1(A_127, B_128, C_129), k3_filter_1(A_127, B_128, C_130)) | ~v1_funct_1(k3_filter_1(A_127, B_128, C_130)) | ~v1_funct_2(k3_filter_1(A_127, B_128, C_129), k2_zfmisc_1(k8_eqrel_1(A_127, B_128), k8_eqrel_1(A_127, B_128)), k8_eqrel_1(A_127, B_128)) | ~v1_funct_1(k3_filter_1(A_127, B_128, C_129)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_127, A_127), A_127))) | ~v1_funct_2(C_130, k2_zfmisc_1(A_127, A_127), A_127) | ~v1_funct_1(C_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_127, A_127), A_127))) | ~v1_funct_2(C_129, k2_zfmisc_1(A_127, A_127), A_127) | ~v1_funct_1(C_129) | ~m1_subset_1(B_128, k1_zfmisc_1(k2_zfmisc_1(A_127, A_127))) | ~v8_relat_2(B_128) | ~v3_relat_2(B_128) | ~v1_partfun1(B_128, A_127) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_10, c_234])).
% 2.79/1.46  tff(c_242, plain, (![A_131, B_132, C_133, C_134]: (r6_binop_1(k8_eqrel_1(A_131, B_132), k3_filter_1(A_131, B_132, C_133), k3_filter_1(A_131, B_132, C_134)) | ~r5_binop_1(k8_eqrel_1(A_131, B_132), k3_filter_1(A_131, B_132, C_133), k3_filter_1(A_131, B_132, C_134)) | ~r4_binop_1(k8_eqrel_1(A_131, B_132), k3_filter_1(A_131, B_132, C_133), k3_filter_1(A_131, B_132, C_134)) | ~v1_funct_1(k3_filter_1(A_131, B_132, C_134)) | ~v1_funct_1(k3_filter_1(A_131, B_132, C_133)) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_131, A_131), A_131))) | ~v1_funct_2(C_134, k2_zfmisc_1(A_131, A_131), A_131) | ~v1_funct_1(C_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_131, A_131), A_131))) | ~v1_funct_2(C_133, k2_zfmisc_1(A_131, A_131), A_131) | ~v1_funct_1(C_133) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_zfmisc_1(A_131, A_131))) | ~v8_relat_2(B_132) | ~v3_relat_2(B_132) | ~v1_partfun1(B_132, A_131) | v1_xboole_0(A_131))), inference(resolution, [status(thm)], [c_12, c_238])).
% 2.79/1.46  tff(c_26, plain, (~r6_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.79/1.46  tff(c_249, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_242, c_26])).
% 2.79/1.46  tff(c_254, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_62, c_75, c_88, c_58, c_71, c_84, c_116, c_124, c_249])).
% 2.79/1.46  tff(c_255, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_254])).
% 2.79/1.46  tff(c_256, plain, (~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_255])).
% 2.79/1.46  tff(c_259, plain, (~r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m2_filter_1('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_256])).
% 2.79/1.46  tff(c_262, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_30, c_137, c_259])).
% 2.79/1.46  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_262])).
% 2.79/1.46  tff(c_265, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_255])).
% 2.79/1.46  tff(c_269, plain, (~r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m2_filter_1('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_265])).
% 2.79/1.46  tff(c_272, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_30, c_131, c_269])).
% 2.79/1.46  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_272])).
% 2.79/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.46  
% 2.79/1.46  Inference rules
% 2.79/1.46  ----------------------
% 2.79/1.46  #Ref     : 0
% 2.79/1.46  #Sup     : 39
% 2.79/1.46  #Fact    : 0
% 2.79/1.46  #Define  : 0
% 2.79/1.46  #Split   : 4
% 2.79/1.46  #Chain   : 0
% 2.79/1.46  #Close   : 0
% 2.79/1.46  
% 2.79/1.46  Ordering : KBO
% 2.79/1.46  
% 2.79/1.46  Simplification rules
% 2.79/1.46  ----------------------
% 2.79/1.46  #Subsume      : 4
% 2.79/1.46  #Demod        : 79
% 2.79/1.46  #Tautology    : 3
% 2.79/1.46  #SimpNegUnit  : 13
% 2.79/1.46  #BackRed      : 0
% 2.79/1.46  
% 2.79/1.46  #Partial instantiations: 0
% 2.79/1.46  #Strategies tried      : 1
% 2.79/1.46  
% 2.79/1.46  Timing (in seconds)
% 2.79/1.46  ----------------------
% 2.79/1.46  Preprocessing        : 0.35
% 2.79/1.46  Parsing              : 0.20
% 2.79/1.46  CNF conversion       : 0.03
% 2.79/1.46  Main loop            : 0.31
% 2.79/1.46  Inferencing          : 0.13
% 2.79/1.46  Reduction            : 0.09
% 2.79/1.46  Demodulation         : 0.06
% 2.79/1.46  BG Simplification    : 0.02
% 2.79/1.46  Subsumption          : 0.06
% 2.79/1.46  Abstraction          : 0.01
% 2.79/1.46  MUC search           : 0.00
% 2.79/1.46  Cooper               : 0.00
% 2.79/1.46  Total                : 0.71
% 2.79/1.46  Index Insertion      : 0.00
% 2.79/1.46  Index Deletion       : 0.00
% 2.79/1.46  Index Matching       : 0.00
% 2.79/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
