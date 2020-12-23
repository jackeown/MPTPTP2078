%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:35 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 638 expanded)
%              Number of leaves         :   39 ( 248 expanded)
%              Depth                    :   17
%              Number of atoms          :  387 (2732 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_eqrel_1,type,(
    k8_eqrel_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(m1_eqrel_1,type,(
    m1_eqrel_1: ( $i * $i ) > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k9_eqrel_1,type,(
    k9_eqrel_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_binop_1,type,(
    r3_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(r1_binop_1,type,(
    r1_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_binop_1,type,(
    r2_binop_1: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_206,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_partfun1(B,A)
              & v3_relat_2(B)
              & v8_relat_2(B)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( m2_filter_1(D,A,B)
                   => ( r3_binop_1(A,C,D)
                     => r3_binop_1(k8_eqrel_1(A,B),k9_eqrel_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r3_binop_1(A,B,C)
          <=> ( r1_binop_1(A,B,C)
              & r2_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

tff(f_161,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m2_filter_1(D,A,B)
                 => ( r1_binop_1(A,C,D)
                   => r1_binop_1(k8_eqrel_1(A,B),k9_eqrel_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).

tff(f_183,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m2_filter_1(D,A,B)
                 => ( r2_binop_1(A,C,D)
                   => r2_binop_1(k8_eqrel_1(A,B),k9_eqrel_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_eqrel_1(k8_eqrel_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_eqrel_1(B,A)
         => ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_eqrel_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( m1_eqrel_1(B,A)
     => m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_96,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_54,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_52,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_46,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_44,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_58,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_74,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_funct_1(C_82)
      | ~ m2_filter_1(C_82,A_83,B_84)
      | ~ v1_relat_1(B_84)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_77,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_80,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_77])).

tff(c_81,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_80])).

tff(c_83,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_funct_2(C_87,k2_zfmisc_1(A_88,A_88),A_88)
      | ~ m2_filter_1(C_87,A_88,B_89)
      | ~ v1_relat_1(B_89)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_85,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_83])).

tff(c_88,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_85])).

tff(c_89,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_88])).

tff(c_101,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_97,A_97),A_97)))
      | ~ m2_filter_1(C_96,A_97,B_98)
      | ~ v1_relat_1(B_98)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_103,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_106,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_103])).

tff(c_107,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_106])).

tff(c_42,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_148,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_binop_1(A_107,B_108,C_109)
      | ~ r3_binop_1(A_107,B_108,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_107,A_107),A_107)))
      | ~ v1_funct_2(C_109,k2_zfmisc_1(A_107,A_107),A_107)
      | ~ v1_funct_1(C_109)
      | ~ m1_subset_1(B_108,A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_150,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_148])).

tff(c_153,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_81,c_89,c_107,c_150])).

tff(c_36,plain,(
    ! [A_32,B_40,C_44,D_46] :
      ( r1_binop_1(k8_eqrel_1(A_32,B_40),k9_eqrel_1(A_32,B_40,C_44),k3_filter_1(A_32,B_40,D_46))
      | ~ r1_binop_1(A_32,C_44,D_46)
      | ~ m2_filter_1(D_46,A_32,B_40)
      | ~ m1_subset_1(C_44,A_32)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v8_relat_2(B_40)
      | ~ v3_relat_2(B_40)
      | ~ v1_partfun1(B_40,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_138,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_binop_1(A_101,B_102,C_103)
      | ~ r3_binop_1(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_101,A_101),A_101)))
      | ~ v1_funct_2(C_103,k2_zfmisc_1(A_101,A_101),A_101)
      | ~ v1_funct_1(C_103)
      | ~ m1_subset_1(B_102,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_140,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_138])).

tff(c_143,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_81,c_89,c_107,c_140])).

tff(c_38,plain,(
    ! [A_47,B_55,C_59,D_61] :
      ( r2_binop_1(k8_eqrel_1(A_47,B_55),k9_eqrel_1(A_47,B_55,C_59),k3_filter_1(A_47,B_55,D_61))
      | ~ r2_binop_1(A_47,C_59,D_61)
      | ~ m2_filter_1(D_61,A_47,B_55)
      | ~ m1_subset_1(C_59,A_47)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_zfmisc_1(A_47,A_47)))
      | ~ v8_relat_2(B_55)
      | ~ v3_relat_2(B_55)
      | ~ v1_partfun1(B_55,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_125,plain,(
    ! [A_99,B_100] :
      ( m1_eqrel_1(k8_eqrel_1(A_99,B_100),A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v1_partfun1(B_100,A_99)
      | ~ v8_relat_2(B_100)
      | ~ v3_relat_2(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_128,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_131,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_128])).

tff(c_10,plain,(
    ! [B_13,A_11] :
      ( ~ v1_xboole_0(B_13)
      | ~ m1_eqrel_1(B_13,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_134,plain,
    ( ~ v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_137,plain,(
    ~ v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_134])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ m1_eqrel_1(B_27,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_154,plain,(
    ! [A_110,B_111,C_112] :
      ( m2_subset_1(k9_eqrel_1(A_110,B_111,C_112),k1_zfmisc_1(A_110),k8_eqrel_1(A_110,B_111))
      | ~ m1_subset_1(C_112,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v1_partfun1(B_111,A_110)
      | ~ v8_relat_2(B_111)
      | ~ v3_relat_2(B_111)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    ! [C_10,B_8,A_7] :
      ( m1_subset_1(C_10,B_8)
      | ~ m2_subset_1(C_10,A_7,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7))
      | v1_xboole_0(B_8)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [A_129,B_130,C_131] :
      ( m1_subset_1(k9_eqrel_1(A_129,B_130,C_131),k8_eqrel_1(A_129,B_130))
      | ~ m1_subset_1(k8_eqrel_1(A_129,B_130),k1_zfmisc_1(k1_zfmisc_1(A_129)))
      | v1_xboole_0(k8_eqrel_1(A_129,B_130))
      | v1_xboole_0(k1_zfmisc_1(A_129))
      | ~ m1_subset_1(C_131,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(A_129,A_129)))
      | ~ v1_partfun1(B_130,A_129)
      | ~ v8_relat_2(B_130)
      | ~ v3_relat_2(B_130)
      | v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_154,c_6])).

tff(c_195,plain,(
    ! [A_26,B_130,C_131] :
      ( m1_subset_1(k9_eqrel_1(A_26,B_130,C_131),k8_eqrel_1(A_26,B_130))
      | v1_xboole_0(k8_eqrel_1(A_26,B_130))
      | v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ m1_subset_1(C_131,A_26)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ v1_partfun1(B_130,A_26)
      | ~ v8_relat_2(B_130)
      | ~ v3_relat_2(B_130)
      | v1_xboole_0(A_26)
      | ~ m1_eqrel_1(k8_eqrel_1(A_26,B_130),A_26) ) ),
    inference(resolution,[status(thm)],[c_28,c_191])).

tff(c_175,plain,(
    ! [A_117,B_118,C_119] :
      ( v1_funct_1(k3_filter_1(A_117,B_118,C_119))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_117,A_117),A_117)))
      | ~ v1_funct_2(C_119,k2_zfmisc_1(A_117,A_117),A_117)
      | ~ v1_funct_1(C_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v8_relat_2(B_118)
      | ~ v3_relat_2(B_118)
      | ~ v1_partfun1(B_118,A_117)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_177,plain,(
    ! [B_118] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_118,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_118)
      | ~ v3_relat_2(B_118)
      | ~ v1_partfun1(B_118,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_107,c_175])).

tff(c_180,plain,(
    ! [B_118] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_118,'#skF_4'))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_118)
      | ~ v3_relat_2(B_118)
      | ~ v1_partfun1(B_118,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_89,c_177])).

tff(c_182,plain,(
    ! [B_120] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_120,'#skF_4'))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_120)
      | ~ v3_relat_2(B_120)
      | ~ v1_partfun1(B_120,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_180])).

tff(c_185,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_182])).

tff(c_188,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_185])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( v1_funct_2(k3_filter_1(A_18,B_19,C_20),k2_zfmisc_1(k8_eqrel_1(A_18,B_19),k8_eqrel_1(A_18,B_19)),k8_eqrel_1(A_18,B_19))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_18,A_18),A_18)))
      | ~ v1_funct_2(C_20,k2_zfmisc_1(A_18,A_18),A_18)
      | ~ v1_funct_1(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v8_relat_2(B_19)
      | ~ v3_relat_2(B_19)
      | ~ v1_partfun1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_198,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_subset_1(k3_filter_1(A_138,B_139,C_140),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_138,B_139),k8_eqrel_1(A_138,B_139)),k8_eqrel_1(A_138,B_139))))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_138,A_138),A_138)))
      | ~ v1_funct_2(C_140,k2_zfmisc_1(A_138,A_138),A_138)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v8_relat_2(B_139)
      | ~ v3_relat_2(B_139)
      | ~ v1_partfun1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_14,B_15,C_17] :
      ( r3_binop_1(A_14,B_15,C_17)
      | ~ r2_binop_1(A_14,B_15,C_17)
      | ~ r1_binop_1(A_14,B_15,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_14,A_14),A_14)))
      | ~ v1_funct_2(C_17,k2_zfmisc_1(A_14,A_14),A_14)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_238,plain,(
    ! [A_152,B_153,B_154,C_155] :
      ( r3_binop_1(k8_eqrel_1(A_152,B_153),B_154,k3_filter_1(A_152,B_153,C_155))
      | ~ r2_binop_1(k8_eqrel_1(A_152,B_153),B_154,k3_filter_1(A_152,B_153,C_155))
      | ~ r1_binop_1(k8_eqrel_1(A_152,B_153),B_154,k3_filter_1(A_152,B_153,C_155))
      | ~ v1_funct_2(k3_filter_1(A_152,B_153,C_155),k2_zfmisc_1(k8_eqrel_1(A_152,B_153),k8_eqrel_1(A_152,B_153)),k8_eqrel_1(A_152,B_153))
      | ~ v1_funct_1(k3_filter_1(A_152,B_153,C_155))
      | ~ m1_subset_1(B_154,k8_eqrel_1(A_152,B_153))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_152,A_152),A_152)))
      | ~ v1_funct_2(C_155,k2_zfmisc_1(A_152,A_152),A_152)
      | ~ v1_funct_1(C_155)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v8_relat_2(B_153)
      | ~ v3_relat_2(B_153)
      | ~ v1_partfun1(B_153,A_152)
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_198,c_12])).

tff(c_242,plain,(
    ! [A_156,B_157,B_158,C_159] :
      ( r3_binop_1(k8_eqrel_1(A_156,B_157),B_158,k3_filter_1(A_156,B_157,C_159))
      | ~ r2_binop_1(k8_eqrel_1(A_156,B_157),B_158,k3_filter_1(A_156,B_157,C_159))
      | ~ r1_binop_1(k8_eqrel_1(A_156,B_157),B_158,k3_filter_1(A_156,B_157,C_159))
      | ~ v1_funct_1(k3_filter_1(A_156,B_157,C_159))
      | ~ m1_subset_1(B_158,k8_eqrel_1(A_156,B_157))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_156,A_156),A_156)))
      | ~ v1_funct_2(C_159,k2_zfmisc_1(A_156,A_156),A_156)
      | ~ v1_funct_1(C_159)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_zfmisc_1(A_156,A_156)))
      | ~ v8_relat_2(B_157)
      | ~ v3_relat_2(B_157)
      | ~ v1_partfun1(B_157,A_156)
      | v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_20,c_238])).

tff(c_246,plain,(
    ! [B_157,B_158] :
      ( r3_binop_1(k8_eqrel_1('#skF_1',B_157),B_158,k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_1',B_157),B_158,k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_1',B_157),B_158,k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ m1_subset_1(B_158,k8_eqrel_1('#skF_1',B_157))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_157)
      | ~ v3_relat_2(B_157)
      | ~ v1_partfun1(B_157,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_107,c_242])).

tff(c_250,plain,(
    ! [B_157,B_158] :
      ( r3_binop_1(k8_eqrel_1('#skF_1',B_157),B_158,k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_1',B_157),B_158,k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_1',B_157),B_158,k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1',B_157,'#skF_4'))
      | ~ m1_subset_1(B_158,k8_eqrel_1('#skF_1',B_157))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_157)
      | ~ v3_relat_2(B_157)
      | ~ v1_partfun1(B_157,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_89,c_246])).

tff(c_252,plain,(
    ! [B_160,B_161] :
      ( r3_binop_1(k8_eqrel_1('#skF_1',B_160),B_161,k3_filter_1('#skF_1',B_160,'#skF_4'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_1',B_160),B_161,k3_filter_1('#skF_1',B_160,'#skF_4'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_1',B_160),B_161,k3_filter_1('#skF_1',B_160,'#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1',B_160,'#skF_4'))
      | ~ m1_subset_1(B_161,k8_eqrel_1('#skF_1',B_160))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_160)
      | ~ v3_relat_2(B_160)
      | ~ v1_partfun1(B_160,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_250])).

tff(c_40,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_259,plain,
    ( ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k8_eqrel_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_252,c_40])).

tff(c_264,plain,
    ( ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_188,c_259])).

tff(c_265,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_272,plain,
    ( v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | v1_xboole_0('#skF_1')
    | ~ m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_195,c_265])).

tff(c_275,plain,
    ( v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_52,c_50,c_54,c_48,c_46,c_272])).

tff(c_276,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_137,c_275])).

tff(c_64,plain,(
    ! [B_80,A_81] :
      ( v1_xboole_0(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [B_27,A_26] :
      ( v1_xboole_0(B_27)
      | ~ v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ m1_eqrel_1(B_27,A_26) ) ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_280,plain,(
    ! [B_166] :
      ( v1_xboole_0(B_166)
      | ~ m1_eqrel_1(B_166,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_276,c_71])).

tff(c_283,plain,(
    v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_131,c_280])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_283])).

tff(c_288,plain,
    ( ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_290,plain,(
    ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_293,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_290])).

tff(c_296,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_143,c_293])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_296])).

tff(c_299,plain,(
    ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_303,plain,
    ( ~ r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_299])).

tff(c_306,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_153,c_303])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.41  
% 2.81/1.41  %Foreground sorts:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Background operators:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Foreground operators:
% 2.81/1.41  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 2.81/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.41  tff(m1_eqrel_1, type, m1_eqrel_1: ($i * $i) > $o).
% 2.81/1.41  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.81/1.41  tff(k9_eqrel_1, type, k9_eqrel_1: ($i * $i * $i) > $i).
% 2.81/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.41  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 2.81/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.41  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.81/1.41  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 2.81/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.41  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.41  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 2.81/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.41  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 2.81/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.41  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 2.81/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.41  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 2.81/1.41  
% 3.07/1.44  tff(f_206, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r3_binop_1(A, C, D) => r3_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_filter_1)).
% 3.07/1.44  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.44  tff(f_139, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.07/1.44  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_binop_1)).
% 3.07/1.44  tff(f_161, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r1_binop_1(A, C, D) => r1_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_filter_1)).
% 3.07/1.44  tff(f_183, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r2_binop_1(A, C, D) => r2_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_filter_1)).
% 3.07/1.44  tff(f_106, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => m1_eqrel_1(k8_eqrel_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_eqrel_1)).
% 3.07/1.44  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_eqrel_1(B, A) => ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_eqrel_1)).
% 3.07/1.44  tff(f_125, axiom, (![A, B]: (m1_eqrel_1(B, A) => m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_eqrel_1)).
% 3.07/1.44  tff(f_121, axiom, (![A, B, C]: ((((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & m1_subset_1(C, A)) => m2_subset_1(k9_eqrel_1(A, B, C), k1_zfmisc_1(A), k8_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 3.07/1.44  tff(f_49, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 3.07/1.44  tff(f_96, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.07/1.44  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.07/1.44  tff(c_56, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_54, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_52, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_50, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_46, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_44, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_58, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.44  tff(c_62, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_58])).
% 3.07/1.44  tff(c_74, plain, (![C_82, A_83, B_84]: (v1_funct_1(C_82) | ~m2_filter_1(C_82, A_83, B_84) | ~v1_relat_1(B_84) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.44  tff(c_77, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_74])).
% 3.07/1.44  tff(c_80, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_77])).
% 3.07/1.44  tff(c_81, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_80])).
% 3.07/1.44  tff(c_83, plain, (![C_87, A_88, B_89]: (v1_funct_2(C_87, k2_zfmisc_1(A_88, A_88), A_88) | ~m2_filter_1(C_87, A_88, B_89) | ~v1_relat_1(B_89) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.44  tff(c_85, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_83])).
% 3.07/1.44  tff(c_88, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_85])).
% 3.07/1.44  tff(c_89, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_88])).
% 3.07/1.44  tff(c_101, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_97, A_97), A_97))) | ~m2_filter_1(C_96, A_97, B_98) | ~v1_relat_1(B_98) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.44  tff(c_103, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_101])).
% 3.07/1.44  tff(c_106, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_103])).
% 3.07/1.44  tff(c_107, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_106])).
% 3.07/1.44  tff(c_42, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_148, plain, (![A_107, B_108, C_109]: (r1_binop_1(A_107, B_108, C_109) | ~r3_binop_1(A_107, B_108, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_107, A_107), A_107))) | ~v1_funct_2(C_109, k2_zfmisc_1(A_107, A_107), A_107) | ~v1_funct_1(C_109) | ~m1_subset_1(B_108, A_107))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.44  tff(c_150, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_148])).
% 3.07/1.44  tff(c_153, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_81, c_89, c_107, c_150])).
% 3.07/1.44  tff(c_36, plain, (![A_32, B_40, C_44, D_46]: (r1_binop_1(k8_eqrel_1(A_32, B_40), k9_eqrel_1(A_32, B_40, C_44), k3_filter_1(A_32, B_40, D_46)) | ~r1_binop_1(A_32, C_44, D_46) | ~m2_filter_1(D_46, A_32, B_40) | ~m1_subset_1(C_44, A_32) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v8_relat_2(B_40) | ~v3_relat_2(B_40) | ~v1_partfun1(B_40, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.07/1.44  tff(c_138, plain, (![A_101, B_102, C_103]: (r2_binop_1(A_101, B_102, C_103) | ~r3_binop_1(A_101, B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_101, A_101), A_101))) | ~v1_funct_2(C_103, k2_zfmisc_1(A_101, A_101), A_101) | ~v1_funct_1(C_103) | ~m1_subset_1(B_102, A_101))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.44  tff(c_140, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_138])).
% 3.07/1.44  tff(c_143, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_81, c_89, c_107, c_140])).
% 3.07/1.44  tff(c_38, plain, (![A_47, B_55, C_59, D_61]: (r2_binop_1(k8_eqrel_1(A_47, B_55), k9_eqrel_1(A_47, B_55, C_59), k3_filter_1(A_47, B_55, D_61)) | ~r2_binop_1(A_47, C_59, D_61) | ~m2_filter_1(D_61, A_47, B_55) | ~m1_subset_1(C_59, A_47) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))) | ~v8_relat_2(B_55) | ~v3_relat_2(B_55) | ~v1_partfun1(B_55, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.07/1.44  tff(c_125, plain, (![A_99, B_100]: (m1_eqrel_1(k8_eqrel_1(A_99, B_100), A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v1_partfun1(B_100, A_99) | ~v8_relat_2(B_100) | ~v3_relat_2(B_100))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.07/1.44  tff(c_128, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_48, c_125])).
% 3.07/1.44  tff(c_131, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_54, c_128])).
% 3.07/1.44  tff(c_10, plain, (![B_13, A_11]: (~v1_xboole_0(B_13) | ~m1_eqrel_1(B_13, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.44  tff(c_134, plain, (~v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_131, c_10])).
% 3.07/1.44  tff(c_137, plain, (~v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_134])).
% 3.07/1.44  tff(c_28, plain, (![B_27, A_26]: (m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~m1_eqrel_1(B_27, A_26))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.07/1.44  tff(c_154, plain, (![A_110, B_111, C_112]: (m2_subset_1(k9_eqrel_1(A_110, B_111, C_112), k1_zfmisc_1(A_110), k8_eqrel_1(A_110, B_111)) | ~m1_subset_1(C_112, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v1_partfun1(B_111, A_110) | ~v8_relat_2(B_111) | ~v3_relat_2(B_111) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.07/1.44  tff(c_6, plain, (![C_10, B_8, A_7]: (m1_subset_1(C_10, B_8) | ~m2_subset_1(C_10, A_7, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)) | v1_xboole_0(B_8) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.44  tff(c_191, plain, (![A_129, B_130, C_131]: (m1_subset_1(k9_eqrel_1(A_129, B_130, C_131), k8_eqrel_1(A_129, B_130)) | ~m1_subset_1(k8_eqrel_1(A_129, B_130), k1_zfmisc_1(k1_zfmisc_1(A_129))) | v1_xboole_0(k8_eqrel_1(A_129, B_130)) | v1_xboole_0(k1_zfmisc_1(A_129)) | ~m1_subset_1(C_131, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_zfmisc_1(A_129, A_129))) | ~v1_partfun1(B_130, A_129) | ~v8_relat_2(B_130) | ~v3_relat_2(B_130) | v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_154, c_6])).
% 3.07/1.44  tff(c_195, plain, (![A_26, B_130, C_131]: (m1_subset_1(k9_eqrel_1(A_26, B_130, C_131), k8_eqrel_1(A_26, B_130)) | v1_xboole_0(k8_eqrel_1(A_26, B_130)) | v1_xboole_0(k1_zfmisc_1(A_26)) | ~m1_subset_1(C_131, A_26) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~v1_partfun1(B_130, A_26) | ~v8_relat_2(B_130) | ~v3_relat_2(B_130) | v1_xboole_0(A_26) | ~m1_eqrel_1(k8_eqrel_1(A_26, B_130), A_26))), inference(resolution, [status(thm)], [c_28, c_191])).
% 3.07/1.44  tff(c_175, plain, (![A_117, B_118, C_119]: (v1_funct_1(k3_filter_1(A_117, B_118, C_119)) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_117, A_117), A_117))) | ~v1_funct_2(C_119, k2_zfmisc_1(A_117, A_117), A_117) | ~v1_funct_1(C_119) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v8_relat_2(B_118) | ~v3_relat_2(B_118) | ~v1_partfun1(B_118, A_117) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.07/1.44  tff(c_177, plain, (![B_118]: (v1_funct_1(k3_filter_1('#skF_1', B_118, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_118) | ~v3_relat_2(B_118) | ~v1_partfun1(B_118, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_107, c_175])).
% 3.07/1.44  tff(c_180, plain, (![B_118]: (v1_funct_1(k3_filter_1('#skF_1', B_118, '#skF_4')) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_118) | ~v3_relat_2(B_118) | ~v1_partfun1(B_118, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_89, c_177])).
% 3.07/1.44  tff(c_182, plain, (![B_120]: (v1_funct_1(k3_filter_1('#skF_1', B_120, '#skF_4')) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_120) | ~v3_relat_2(B_120) | ~v1_partfun1(B_120, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_180])).
% 3.07/1.44  tff(c_185, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_182])).
% 3.07/1.44  tff(c_188, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_185])).
% 3.07/1.44  tff(c_20, plain, (![A_18, B_19, C_20]: (v1_funct_2(k3_filter_1(A_18, B_19, C_20), k2_zfmisc_1(k8_eqrel_1(A_18, B_19), k8_eqrel_1(A_18, B_19)), k8_eqrel_1(A_18, B_19)) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_18, A_18), A_18))) | ~v1_funct_2(C_20, k2_zfmisc_1(A_18, A_18), A_18) | ~v1_funct_1(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v8_relat_2(B_19) | ~v3_relat_2(B_19) | ~v1_partfun1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.07/1.44  tff(c_198, plain, (![A_138, B_139, C_140]: (m1_subset_1(k3_filter_1(A_138, B_139, C_140), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_138, B_139), k8_eqrel_1(A_138, B_139)), k8_eqrel_1(A_138, B_139)))) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_138, A_138), A_138))) | ~v1_funct_2(C_140, k2_zfmisc_1(A_138, A_138), A_138) | ~v1_funct_1(C_140) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v8_relat_2(B_139) | ~v3_relat_2(B_139) | ~v1_partfun1(B_139, A_138) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.07/1.44  tff(c_12, plain, (![A_14, B_15, C_17]: (r3_binop_1(A_14, B_15, C_17) | ~r2_binop_1(A_14, B_15, C_17) | ~r1_binop_1(A_14, B_15, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_14, A_14), A_14))) | ~v1_funct_2(C_17, k2_zfmisc_1(A_14, A_14), A_14) | ~v1_funct_1(C_17) | ~m1_subset_1(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.44  tff(c_238, plain, (![A_152, B_153, B_154, C_155]: (r3_binop_1(k8_eqrel_1(A_152, B_153), B_154, k3_filter_1(A_152, B_153, C_155)) | ~r2_binop_1(k8_eqrel_1(A_152, B_153), B_154, k3_filter_1(A_152, B_153, C_155)) | ~r1_binop_1(k8_eqrel_1(A_152, B_153), B_154, k3_filter_1(A_152, B_153, C_155)) | ~v1_funct_2(k3_filter_1(A_152, B_153, C_155), k2_zfmisc_1(k8_eqrel_1(A_152, B_153), k8_eqrel_1(A_152, B_153)), k8_eqrel_1(A_152, B_153)) | ~v1_funct_1(k3_filter_1(A_152, B_153, C_155)) | ~m1_subset_1(B_154, k8_eqrel_1(A_152, B_153)) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_152, A_152), A_152))) | ~v1_funct_2(C_155, k2_zfmisc_1(A_152, A_152), A_152) | ~v1_funct_1(C_155) | ~m1_subset_1(B_153, k1_zfmisc_1(k2_zfmisc_1(A_152, A_152))) | ~v8_relat_2(B_153) | ~v3_relat_2(B_153) | ~v1_partfun1(B_153, A_152) | v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_198, c_12])).
% 3.07/1.44  tff(c_242, plain, (![A_156, B_157, B_158, C_159]: (r3_binop_1(k8_eqrel_1(A_156, B_157), B_158, k3_filter_1(A_156, B_157, C_159)) | ~r2_binop_1(k8_eqrel_1(A_156, B_157), B_158, k3_filter_1(A_156, B_157, C_159)) | ~r1_binop_1(k8_eqrel_1(A_156, B_157), B_158, k3_filter_1(A_156, B_157, C_159)) | ~v1_funct_1(k3_filter_1(A_156, B_157, C_159)) | ~m1_subset_1(B_158, k8_eqrel_1(A_156, B_157)) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_156, A_156), A_156))) | ~v1_funct_2(C_159, k2_zfmisc_1(A_156, A_156), A_156) | ~v1_funct_1(C_159) | ~m1_subset_1(B_157, k1_zfmisc_1(k2_zfmisc_1(A_156, A_156))) | ~v8_relat_2(B_157) | ~v3_relat_2(B_157) | ~v1_partfun1(B_157, A_156) | v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_20, c_238])).
% 3.07/1.44  tff(c_246, plain, (![B_157, B_158]: (r3_binop_1(k8_eqrel_1('#skF_1', B_157), B_158, k3_filter_1('#skF_1', B_157, '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', B_157), B_158, k3_filter_1('#skF_1', B_157, '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', B_157), B_158, k3_filter_1('#skF_1', B_157, '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', B_157, '#skF_4')) | ~m1_subset_1(B_158, k8_eqrel_1('#skF_1', B_157)) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_157, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_157) | ~v3_relat_2(B_157) | ~v1_partfun1(B_157, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_107, c_242])).
% 3.07/1.44  tff(c_250, plain, (![B_157, B_158]: (r3_binop_1(k8_eqrel_1('#skF_1', B_157), B_158, k3_filter_1('#skF_1', B_157, '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', B_157), B_158, k3_filter_1('#skF_1', B_157, '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', B_157), B_158, k3_filter_1('#skF_1', B_157, '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', B_157, '#skF_4')) | ~m1_subset_1(B_158, k8_eqrel_1('#skF_1', B_157)) | ~m1_subset_1(B_157, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_157) | ~v3_relat_2(B_157) | ~v1_partfun1(B_157, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_89, c_246])).
% 3.07/1.44  tff(c_252, plain, (![B_160, B_161]: (r3_binop_1(k8_eqrel_1('#skF_1', B_160), B_161, k3_filter_1('#skF_1', B_160, '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', B_160), B_161, k3_filter_1('#skF_1', B_160, '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', B_160), B_161, k3_filter_1('#skF_1', B_160, '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', B_160, '#skF_4')) | ~m1_subset_1(B_161, k8_eqrel_1('#skF_1', B_160)) | ~m1_subset_1(B_160, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_160) | ~v3_relat_2(B_160) | ~v1_partfun1(B_160, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_250])).
% 3.07/1.44  tff(c_40, plain, (~r3_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.07/1.44  tff(c_259, plain, (~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k8_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_252, c_40])).
% 3.07/1.44  tff(c_264, plain, (~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k8_eqrel_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_188, c_259])).
% 3.07/1.44  tff(c_265, plain, (~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k8_eqrel_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_264])).
% 3.07/1.44  tff(c_272, plain, (v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1') | ~m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_195, c_265])).
% 3.07/1.44  tff(c_275, plain, (v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_52, c_50, c_54, c_48, c_46, c_272])).
% 3.07/1.44  tff(c_276, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_137, c_275])).
% 3.07/1.44  tff(c_64, plain, (![B_80, A_81]: (v1_xboole_0(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.44  tff(c_71, plain, (![B_27, A_26]: (v1_xboole_0(B_27) | ~v1_xboole_0(k1_zfmisc_1(A_26)) | ~m1_eqrel_1(B_27, A_26))), inference(resolution, [status(thm)], [c_28, c_64])).
% 3.07/1.44  tff(c_280, plain, (![B_166]: (v1_xboole_0(B_166) | ~m1_eqrel_1(B_166, '#skF_1'))), inference(resolution, [status(thm)], [c_276, c_71])).
% 3.07/1.44  tff(c_283, plain, (v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_131, c_280])).
% 3.07/1.44  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_283])).
% 3.07/1.44  tff(c_288, plain, (~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_264])).
% 3.07/1.44  tff(c_290, plain, (~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_288])).
% 3.07/1.44  tff(c_293, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_290])).
% 3.07/1.44  tff(c_296, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_44, c_143, c_293])).
% 3.07/1.44  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_296])).
% 3.07/1.44  tff(c_299, plain, (~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_288])).
% 3.07/1.44  tff(c_303, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_299])).
% 3.07/1.44  tff(c_306, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_44, c_153, c_303])).
% 3.07/1.44  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_306])).
% 3.07/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.44  
% 3.07/1.44  Inference rules
% 3.07/1.44  ----------------------
% 3.07/1.44  #Ref     : 0
% 3.07/1.44  #Sup     : 44
% 3.07/1.44  #Fact    : 0
% 3.07/1.44  #Define  : 0
% 3.07/1.44  #Split   : 7
% 3.07/1.44  #Chain   : 0
% 3.07/1.44  #Close   : 0
% 3.07/1.44  
% 3.07/1.44  Ordering : KBO
% 3.07/1.44  
% 3.07/1.44  Simplification rules
% 3.07/1.44  ----------------------
% 3.07/1.44  #Subsume      : 2
% 3.07/1.44  #Demod        : 59
% 3.07/1.44  #Tautology    : 6
% 3.07/1.44  #SimpNegUnit  : 13
% 3.07/1.44  #BackRed      : 0
% 3.07/1.44  
% 3.07/1.44  #Partial instantiations: 0
% 3.07/1.44  #Strategies tried      : 1
% 3.07/1.44  
% 3.07/1.44  Timing (in seconds)
% 3.07/1.44  ----------------------
% 3.07/1.44  Preprocessing        : 0.34
% 3.07/1.44  Parsing              : 0.19
% 3.07/1.44  CNF conversion       : 0.03
% 3.07/1.44  Main loop            : 0.33
% 3.07/1.44  Inferencing          : 0.13
% 3.07/1.44  Reduction            : 0.09
% 3.07/1.44  Demodulation         : 0.06
% 3.07/1.44  BG Simplification    : 0.02
% 3.07/1.44  Subsumption          : 0.07
% 3.07/1.44  Abstraction          : 0.01
% 3.07/1.45  MUC search           : 0.00
% 3.07/1.45  Cooper               : 0.00
% 3.07/1.45  Total                : 0.72
% 3.07/1.45  Index Insertion      : 0.00
% 3.07/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
