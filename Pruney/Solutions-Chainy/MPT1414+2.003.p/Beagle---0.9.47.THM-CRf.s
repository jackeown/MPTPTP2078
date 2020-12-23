%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:36 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  132 (1044 expanded)
%              Number of leaves         :   39 ( 409 expanded)
%              Depth                    :   15
%              Number of atoms          :  436 (4560 expanded)
%              Number of equality atoms :    4 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_eqrel_1,type,(
    k8_eqrel_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_eqrel_1,type,(
    k7_eqrel_1: ( $i * $i ) > $i )).

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

tff(f_217,negated_conjecture,(
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

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_64,axiom,(
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

tff(f_150,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k8_eqrel_1(A,B) = k7_eqrel_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

tff(f_172,axiom,(
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

tff(f_194,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_subset_1(k7_eqrel_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ~ v1_xboole_0(k7_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_eqrel_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_112,axiom,(
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

tff(f_87,axiom,(
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

tff(c_46,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_44,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_63,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_68,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_funct_1(C_77)
      | ~ m2_filter_1(C_77,A_78,B_79)
      | ~ v1_relat_1(B_79)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_71,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_74,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_71])).

tff(c_75,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_74])).

tff(c_76,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_funct_2(C_80,k2_zfmisc_1(A_81,A_81),A_81)
      | ~ m2_filter_1(C_80,A_81,B_82)
      | ~ v1_relat_1(B_82)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_78,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_81,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_81])).

tff(c_91,plain,(
    ! [C_89,A_90,B_91] :
      ( m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_90,A_90),A_90)))
      | ~ m2_filter_1(C_89,A_90,B_91)
      | ~ v1_relat_1(B_91)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_93,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_91])).

tff(c_96,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_93])).

tff(c_97,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_96])).

tff(c_42,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_154,plain,(
    ! [A_103,B_104,C_105] :
      ( r1_binop_1(A_103,B_104,C_105)
      | ~ r3_binop_1(A_103,B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_103,A_103),A_103)))
      | ~ v1_funct_2(C_105,k2_zfmisc_1(A_103,A_103),A_103)
      | ~ v1_funct_1(C_105)
      | ~ m1_subset_1(B_104,A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_156,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_159,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75,c_82,c_97,c_156])).

tff(c_54,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_52,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_50,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_120,plain,(
    ! [A_94,B_95] :
      ( k8_eqrel_1(A_94,B_95) = k7_eqrel_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(A_94,A_94)))
      | ~ v1_partfun1(B_95,A_94)
      | ~ v8_relat_2(B_95)
      | ~ v3_relat_2(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_123,plain,
    ( k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_126,plain,(
    k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_123])).

tff(c_246,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( r1_binop_1(k8_eqrel_1(A_127,B_128),k9_eqrel_1(A_127,B_128,C_129),k3_filter_1(A_127,B_128,D_130))
      | ~ r1_binop_1(A_127,C_129,D_130)
      | ~ m2_filter_1(D_130,A_127,B_128)
      | ~ m1_subset_1(C_129,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_zfmisc_1(A_127,A_127)))
      | ~ v8_relat_2(B_128)
      | ~ v3_relat_2(B_128)
      | ~ v1_partfun1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_249,plain,(
    ! [C_129,D_130] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_129),k3_filter_1('#skF_1','#skF_2',D_130))
      | ~ r1_binop_1('#skF_1',C_129,D_130)
      | ~ m2_filter_1(D_130,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_129,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_246])).

tff(c_251,plain,(
    ! [C_129,D_130] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_129),k3_filter_1('#skF_1','#skF_2',D_130))
      | ~ r1_binop_1('#skF_1',C_129,D_130)
      | ~ m2_filter_1(D_130,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_129,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_249])).

tff(c_252,plain,(
    ! [C_129,D_130] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_129),k3_filter_1('#skF_1','#skF_2',D_130))
      | ~ r1_binop_1('#skF_1',C_129,D_130)
      | ~ m2_filter_1(D_130,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_129,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_251])).

tff(c_140,plain,(
    ! [A_98,B_99,C_100] :
      ( r2_binop_1(A_98,B_99,C_100)
      | ~ r3_binop_1(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_98,A_98),A_98)))
      | ~ v1_funct_2(C_100,k2_zfmisc_1(A_98,A_98),A_98)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(B_99,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_142,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_140])).

tff(c_145,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75,c_82,c_97,c_142])).

tff(c_239,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( r2_binop_1(k8_eqrel_1(A_123,B_124),k9_eqrel_1(A_123,B_124,C_125),k3_filter_1(A_123,B_124,D_126))
      | ~ r2_binop_1(A_123,C_125,D_126)
      | ~ m2_filter_1(D_126,A_123,B_124)
      | ~ m1_subset_1(C_125,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1(A_123,A_123)))
      | ~ v8_relat_2(B_124)
      | ~ v3_relat_2(B_124)
      | ~ v1_partfun1(B_124,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_242,plain,(
    ! [C_125,D_126] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_125),k3_filter_1('#skF_1','#skF_2',D_126))
      | ~ r2_binop_1('#skF_1',C_125,D_126)
      | ~ m2_filter_1(D_126,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_125,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_239])).

tff(c_244,plain,(
    ! [C_125,D_126] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_125),k3_filter_1('#skF_1','#skF_2',D_126))
      | ~ r2_binop_1('#skF_1',C_125,D_126)
      | ~ m2_filter_1(D_126,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_125,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_242])).

tff(c_245,plain,(
    ! [C_125,D_126] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_125),k3_filter_1('#skF_1','#skF_2',D_126))
      | ~ r2_binop_1('#skF_1',C_125,D_126)
      | ~ m2_filter_1(D_126,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_125,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_244])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k7_eqrel_1(A_18,B_19),k1_zfmisc_1(k1_zfmisc_1(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v1_partfun1(B_19,A_18)
      | ~ v8_relat_2(B_19)
      | ~ v3_relat_2(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_109,plain,(
    ! [A_92,B_93] :
      ( ~ v1_xboole_0(k7_eqrel_1(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v1_partfun1(B_93,A_92)
      | ~ v8_relat_2(B_93)
      | ~ v3_relat_2(B_93)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_112,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_115,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_112])).

tff(c_116,plain,(
    ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_115])).

tff(c_132,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k7_eqrel_1(A_96,B_97),k1_zfmisc_1(k1_zfmisc_1(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v1_partfun1(B_97,A_96)
      | ~ v8_relat_2(B_97)
      | ~ v3_relat_2(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_101,B_102] :
      ( v1_xboole_0(k7_eqrel_1(A_101,B_102))
      | ~ v1_xboole_0(k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_zfmisc_1(A_101,A_101)))
      | ~ v1_partfun1(B_102,A_101)
      | ~ v8_relat_2(B_102)
      | ~ v3_relat_2(B_102) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_149,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_146])).

tff(c_152,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_149])).

tff(c_153,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_152])).

tff(c_160,plain,(
    ! [A_106,B_107,C_108] :
      ( m2_subset_1(k9_eqrel_1(A_106,B_107,C_108),k1_zfmisc_1(A_106),k8_eqrel_1(A_106,B_107))
      | ~ m1_subset_1(C_108,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v1_partfun1(B_107,A_106)
      | ~ v8_relat_2(B_107)
      | ~ v3_relat_2(B_107)
      | v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_165,plain,(
    ! [C_108] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_108),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_108,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_partfun1('#skF_2','#skF_1')
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_160])).

tff(c_168,plain,(
    ! [C_108] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_108),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_108,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_48,c_165])).

tff(c_170,plain,(
    ! [C_109] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_109),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_109,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_168])).

tff(c_6,plain,(
    ! [C_10,B_8,A_7] :
      ( m1_subset_1(C_10,B_8)
      | ~ m2_subset_1(C_10,A_7,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7))
      | v1_xboole_0(B_8)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [C_109] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_109),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_109,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_170,c_6])).

tff(c_175,plain,(
    ! [C_109] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_109),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(C_109,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_116,c_172])).

tff(c_176,plain,(
    ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_179,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_48,c_179])).

tff(c_184,plain,(
    ! [C_109] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_109),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_109,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_225,plain,(
    ! [A_119,B_120,C_121] :
      ( v1_funct_1(k3_filter_1(A_119,B_120,C_121))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_119,A_119),A_119)))
      | ~ v1_funct_2(C_121,k2_zfmisc_1(A_119,A_119),A_119)
      | ~ v1_funct_1(C_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v8_relat_2(B_120)
      | ~ v3_relat_2(B_120)
      | ~ v1_partfun1(B_120,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_227,plain,(
    ! [B_120] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_120,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_120)
      | ~ v3_relat_2(B_120)
      | ~ v1_partfun1(B_120,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_97,c_225])).

tff(c_230,plain,(
    ! [B_120] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_120,'#skF_4'))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_120)
      | ~ v3_relat_2(B_120)
      | ~ v1_partfun1(B_120,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_82,c_227])).

tff(c_232,plain,(
    ! [B_122] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_122,'#skF_4'))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_122)
      | ~ v3_relat_2(B_122)
      | ~ v1_partfun1(B_122,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_230])).

tff(c_235,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_232])).

tff(c_238,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_235])).

tff(c_261,plain,(
    ! [A_138,B_139,C_140] :
      ( v1_funct_2(k3_filter_1(A_138,B_139,C_140),k2_zfmisc_1(k8_eqrel_1(A_138,B_139),k8_eqrel_1(A_138,B_139)),k8_eqrel_1(A_138,B_139))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_138,A_138),A_138)))
      | ~ v1_funct_2(C_140,k2_zfmisc_1(A_138,A_138),A_138)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v8_relat_2(B_139)
      | ~ v3_relat_2(B_139)
      | ~ v1_partfun1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_264,plain,(
    ! [C_140] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_140),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_140,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_261])).

tff(c_272,plain,(
    ! [C_140] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_140),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_140,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_126,c_126,c_264])).

tff(c_273,plain,(
    ! [C_140] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_140),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_140,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_272])).

tff(c_281,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1(k3_filter_1(A_142,B_143,C_144),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_142,B_143),k8_eqrel_1(A_142,B_143)),k8_eqrel_1(A_142,B_143))))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_142,A_142),A_142)))
      | ~ v1_funct_2(C_144,k2_zfmisc_1(A_142,A_142),A_142)
      | ~ v1_funct_1(C_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_zfmisc_1(A_142,A_142)))
      | ~ v8_relat_2(B_143)
      | ~ v3_relat_2(B_143)
      | ~ v1_partfun1(B_143,A_142)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_296,plain,(
    ! [C_144] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_144),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_144,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_144)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_281])).

tff(c_309,plain,(
    ! [C_144] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_144),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_144,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_144)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_126,c_126,c_296])).

tff(c_317,plain,(
    ! [C_145] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_145),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_145,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_309])).

tff(c_10,plain,(
    ! [A_11,B_12,C_14] :
      ( r3_binop_1(A_11,B_12,C_14)
      | ~ r2_binop_1(A_11,B_12,C_14)
      | ~ r1_binop_1(A_11,B_12,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11,A_11),A_11)))
      | ~ v1_funct_2(C_14,k2_zfmisc_1(A_11,A_11),A_11)
      | ~ v1_funct_1(C_14)
      | ~ m1_subset_1(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_422,plain,(
    ! [B_168,C_169] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_168,k3_filter_1('#skF_1','#skF_2',C_169))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_168,k3_filter_1('#skF_1','#skF_2',C_169))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_168,k3_filter_1('#skF_1','#skF_2',C_169))
      | ~ v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_169),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_169))
      | ~ m1_subset_1(B_168,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_169,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_169) ) ),
    inference(resolution,[status(thm)],[c_317,c_10])).

tff(c_426,plain,(
    ! [B_170,C_171] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_170,k3_filter_1('#skF_1','#skF_2',C_171))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_170,k3_filter_1('#skF_1','#skF_2',C_171))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_170,k3_filter_1('#skF_1','#skF_2',C_171))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_171))
      | ~ m1_subset_1(B_170,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_171,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_171) ) ),
    inference(resolution,[status(thm)],[c_273,c_422])).

tff(c_428,plain,(
    ! [B_170] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_170,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_170,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_170,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_170,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_97,c_426])).

tff(c_432,plain,(
    ! [B_172] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_172,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_172,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_172,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_172,k7_eqrel_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_82,c_238,c_428])).

tff(c_40,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_127,plain,(
    ~ r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_40])).

tff(c_446,plain,
    ( ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_432,c_127])).

tff(c_447,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_450,plain,(
    ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_184,c_447])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_450])).

tff(c_455,plain,
    ( ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_476,plain,(
    ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_479,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_245,c_476])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_145,c_479])).

tff(c_484,plain,(
    ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_488,plain,
    ( ~ r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_252,c_484])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_159,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.60  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.60  
% 3.43/1.60  %Foreground sorts:
% 3.43/1.60  
% 3.43/1.60  
% 3.43/1.60  %Background operators:
% 3.43/1.60  
% 3.43/1.60  
% 3.43/1.60  %Foreground operators:
% 3.43/1.60  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 3.43/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.60  tff(k7_eqrel_1, type, k7_eqrel_1: ($i * $i) > $i).
% 3.43/1.60  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.43/1.60  tff(k9_eqrel_1, type, k9_eqrel_1: ($i * $i * $i) > $i).
% 3.43/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.60  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 3.43/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.43/1.60  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 3.43/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.60  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 3.43/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.60  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 3.43/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.60  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 3.43/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.60  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 3.43/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.60  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 3.43/1.60  
% 3.43/1.63  tff(f_217, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r3_binop_1(A, C, D) => r3_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_filter_1)).
% 3.43/1.63  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.63  tff(f_126, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.43/1.63  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_binop_1)).
% 3.43/1.63  tff(f_150, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k8_eqrel_1(A, B) = k7_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_eqrel_1)).
% 3.43/1.63  tff(f_172, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r1_binop_1(A, C, D) => r1_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_filter_1)).
% 3.43/1.63  tff(f_194, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r2_binop_1(A, C, D) => r2_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_filter_1)).
% 3.43/1.63  tff(f_97, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => m1_subset_1(k7_eqrel_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_eqrel_1)).
% 3.43/1.63  tff(f_140, axiom, (![A, B]: (((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ~v1_xboole_0(k7_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_eqrel_1)).
% 3.43/1.63  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.43/1.63  tff(f_112, axiom, (![A, B, C]: ((((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & m1_subset_1(C, A)) => m2_subset_1(k9_eqrel_1(A, B, C), k1_zfmisc_1(A), k8_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 3.43/1.63  tff(f_49, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 3.43/1.63  tff(f_87, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.43/1.63  tff(c_46, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_44, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_56, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_63, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.43/1.63  tff(c_67, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_63])).
% 3.43/1.63  tff(c_68, plain, (![C_77, A_78, B_79]: (v1_funct_1(C_77) | ~m2_filter_1(C_77, A_78, B_79) | ~v1_relat_1(B_79) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.43/1.63  tff(c_71, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_68])).
% 3.43/1.63  tff(c_74, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_71])).
% 3.43/1.63  tff(c_75, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_74])).
% 3.43/1.63  tff(c_76, plain, (![C_80, A_81, B_82]: (v1_funct_2(C_80, k2_zfmisc_1(A_81, A_81), A_81) | ~m2_filter_1(C_80, A_81, B_82) | ~v1_relat_1(B_82) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.43/1.63  tff(c_78, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_76])).
% 3.43/1.63  tff(c_81, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_78])).
% 3.43/1.63  tff(c_82, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_81])).
% 3.43/1.63  tff(c_91, plain, (![C_89, A_90, B_91]: (m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_90, A_90), A_90))) | ~m2_filter_1(C_89, A_90, B_91) | ~v1_relat_1(B_91) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.43/1.63  tff(c_93, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_91])).
% 3.43/1.63  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_93])).
% 3.43/1.63  tff(c_97, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_96])).
% 3.43/1.63  tff(c_42, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_154, plain, (![A_103, B_104, C_105]: (r1_binop_1(A_103, B_104, C_105) | ~r3_binop_1(A_103, B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_103, A_103), A_103))) | ~v1_funct_2(C_105, k2_zfmisc_1(A_103, A_103), A_103) | ~v1_funct_1(C_105) | ~m1_subset_1(B_104, A_103))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.43/1.63  tff(c_156, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_154])).
% 3.43/1.63  tff(c_159, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75, c_82, c_97, c_156])).
% 3.43/1.63  tff(c_54, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_52, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_50, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_120, plain, (![A_94, B_95]: (k8_eqrel_1(A_94, B_95)=k7_eqrel_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_zfmisc_1(A_94, A_94))) | ~v1_partfun1(B_95, A_94) | ~v8_relat_2(B_95) | ~v3_relat_2(B_95))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.43/1.63  tff(c_123, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_48, c_120])).
% 3.43/1.63  tff(c_126, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_54, c_123])).
% 3.43/1.63  tff(c_246, plain, (![A_127, B_128, C_129, D_130]: (r1_binop_1(k8_eqrel_1(A_127, B_128), k9_eqrel_1(A_127, B_128, C_129), k3_filter_1(A_127, B_128, D_130)) | ~r1_binop_1(A_127, C_129, D_130) | ~m2_filter_1(D_130, A_127, B_128) | ~m1_subset_1(C_129, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(k2_zfmisc_1(A_127, A_127))) | ~v8_relat_2(B_128) | ~v3_relat_2(B_128) | ~v1_partfun1(B_128, A_127) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.43/1.63  tff(c_249, plain, (![C_129, D_130]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_129), k3_filter_1('#skF_1', '#skF_2', D_130)) | ~r1_binop_1('#skF_1', C_129, D_130) | ~m2_filter_1(D_130, '#skF_1', '#skF_2') | ~m1_subset_1(C_129, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_246])).
% 3.43/1.63  tff(c_251, plain, (![C_129, D_130]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_129), k3_filter_1('#skF_1', '#skF_2', D_130)) | ~r1_binop_1('#skF_1', C_129, D_130) | ~m2_filter_1(D_130, '#skF_1', '#skF_2') | ~m1_subset_1(C_129, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_249])).
% 3.43/1.63  tff(c_252, plain, (![C_129, D_130]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_129), k3_filter_1('#skF_1', '#skF_2', D_130)) | ~r1_binop_1('#skF_1', C_129, D_130) | ~m2_filter_1(D_130, '#skF_1', '#skF_2') | ~m1_subset_1(C_129, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_251])).
% 3.43/1.63  tff(c_140, plain, (![A_98, B_99, C_100]: (r2_binop_1(A_98, B_99, C_100) | ~r3_binop_1(A_98, B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_98, A_98), A_98))) | ~v1_funct_2(C_100, k2_zfmisc_1(A_98, A_98), A_98) | ~v1_funct_1(C_100) | ~m1_subset_1(B_99, A_98))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.43/1.63  tff(c_142, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_140])).
% 3.43/1.63  tff(c_145, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75, c_82, c_97, c_142])).
% 3.43/1.63  tff(c_239, plain, (![A_123, B_124, C_125, D_126]: (r2_binop_1(k8_eqrel_1(A_123, B_124), k9_eqrel_1(A_123, B_124, C_125), k3_filter_1(A_123, B_124, D_126)) | ~r2_binop_1(A_123, C_125, D_126) | ~m2_filter_1(D_126, A_123, B_124) | ~m1_subset_1(C_125, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1(A_123, A_123))) | ~v8_relat_2(B_124) | ~v3_relat_2(B_124) | ~v1_partfun1(B_124, A_123) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.43/1.63  tff(c_242, plain, (![C_125, D_126]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_125), k3_filter_1('#skF_1', '#skF_2', D_126)) | ~r2_binop_1('#skF_1', C_125, D_126) | ~m2_filter_1(D_126, '#skF_1', '#skF_2') | ~m1_subset_1(C_125, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_239])).
% 3.43/1.63  tff(c_244, plain, (![C_125, D_126]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_125), k3_filter_1('#skF_1', '#skF_2', D_126)) | ~r2_binop_1('#skF_1', C_125, D_126) | ~m2_filter_1(D_126, '#skF_1', '#skF_2') | ~m1_subset_1(C_125, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_242])).
% 3.43/1.63  tff(c_245, plain, (![C_125, D_126]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_125), k3_filter_1('#skF_1', '#skF_2', D_126)) | ~r2_binop_1('#skF_1', C_125, D_126) | ~m2_filter_1(D_126, '#skF_1', '#skF_2') | ~m1_subset_1(C_125, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_244])).
% 3.43/1.63  tff(c_22, plain, (![A_18, B_19]: (m1_subset_1(k7_eqrel_1(A_18, B_19), k1_zfmisc_1(k1_zfmisc_1(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v1_partfun1(B_19, A_18) | ~v8_relat_2(B_19) | ~v3_relat_2(B_19))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.43/1.63  tff(c_109, plain, (![A_92, B_93]: (~v1_xboole_0(k7_eqrel_1(A_92, B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v1_partfun1(B_93, A_92) | ~v8_relat_2(B_93) | ~v3_relat_2(B_93) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.43/1.63  tff(c_112, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_109])).
% 3.43/1.63  tff(c_115, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_54, c_112])).
% 3.43/1.63  tff(c_116, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_115])).
% 3.43/1.63  tff(c_132, plain, (![A_96, B_97]: (m1_subset_1(k7_eqrel_1(A_96, B_97), k1_zfmisc_1(k1_zfmisc_1(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v1_partfun1(B_97, A_96) | ~v8_relat_2(B_97) | ~v3_relat_2(B_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.43/1.63  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.63  tff(c_146, plain, (![A_101, B_102]: (v1_xboole_0(k7_eqrel_1(A_101, B_102)) | ~v1_xboole_0(k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(k2_zfmisc_1(A_101, A_101))) | ~v1_partfun1(B_102, A_101) | ~v8_relat_2(B_102) | ~v3_relat_2(B_102))), inference(resolution, [status(thm)], [c_132, c_2])).
% 3.43/1.63  tff(c_149, plain, (v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_48, c_146])).
% 3.43/1.63  tff(c_152, plain, (v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_54, c_149])).
% 3.43/1.63  tff(c_153, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_116, c_152])).
% 3.43/1.63  tff(c_160, plain, (![A_106, B_107, C_108]: (m2_subset_1(k9_eqrel_1(A_106, B_107, C_108), k1_zfmisc_1(A_106), k8_eqrel_1(A_106, B_107)) | ~m1_subset_1(C_108, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v1_partfun1(B_107, A_106) | ~v8_relat_2(B_107) | ~v3_relat_2(B_107) | v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.43/1.63  tff(c_165, plain, (![C_108]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_108), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_108, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_160])).
% 3.43/1.63  tff(c_168, plain, (![C_108]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_108), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_108, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_54, c_48, c_165])).
% 3.43/1.63  tff(c_170, plain, (![C_109]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_109), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_109, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_168])).
% 3.43/1.63  tff(c_6, plain, (![C_10, B_8, A_7]: (m1_subset_1(C_10, B_8) | ~m2_subset_1(C_10, A_7, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)) | v1_xboole_0(B_8) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.43/1.63  tff(c_172, plain, (![C_109]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_109), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_109, '#skF_1'))), inference(resolution, [status(thm)], [c_170, c_6])).
% 3.43/1.63  tff(c_175, plain, (![C_109]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_109), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1(C_109, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_153, c_116, c_172])).
% 3.43/1.63  tff(c_176, plain, (~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_175])).
% 3.43/1.63  tff(c_179, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_22, c_176])).
% 3.43/1.63  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_54, c_48, c_179])).
% 3.43/1.63  tff(c_184, plain, (![C_109]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_109), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_109, '#skF_1'))), inference(splitRight, [status(thm)], [c_175])).
% 3.43/1.63  tff(c_225, plain, (![A_119, B_120, C_121]: (v1_funct_1(k3_filter_1(A_119, B_120, C_121)) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_119, A_119), A_119))) | ~v1_funct_2(C_121, k2_zfmisc_1(A_119, A_119), A_119) | ~v1_funct_1(C_121) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v8_relat_2(B_120) | ~v3_relat_2(B_120) | ~v1_partfun1(B_120, A_119) | v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.43/1.63  tff(c_227, plain, (![B_120]: (v1_funct_1(k3_filter_1('#skF_1', B_120, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_120) | ~v3_relat_2(B_120) | ~v1_partfun1(B_120, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_97, c_225])).
% 3.43/1.63  tff(c_230, plain, (![B_120]: (v1_funct_1(k3_filter_1('#skF_1', B_120, '#skF_4')) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_120) | ~v3_relat_2(B_120) | ~v1_partfun1(B_120, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_82, c_227])).
% 3.43/1.63  tff(c_232, plain, (![B_122]: (v1_funct_1(k3_filter_1('#skF_1', B_122, '#skF_4')) | ~m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_122) | ~v3_relat_2(B_122) | ~v1_partfun1(B_122, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_230])).
% 3.43/1.63  tff(c_235, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_232])).
% 3.43/1.63  tff(c_238, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_235])).
% 3.43/1.63  tff(c_261, plain, (![A_138, B_139, C_140]: (v1_funct_2(k3_filter_1(A_138, B_139, C_140), k2_zfmisc_1(k8_eqrel_1(A_138, B_139), k8_eqrel_1(A_138, B_139)), k8_eqrel_1(A_138, B_139)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_138, A_138), A_138))) | ~v1_funct_2(C_140, k2_zfmisc_1(A_138, A_138), A_138) | ~v1_funct_1(C_140) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v8_relat_2(B_139) | ~v3_relat_2(B_139) | ~v1_partfun1(B_139, A_138) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.43/1.63  tff(c_264, plain, (![C_140]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_140), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_140, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_140) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_261])).
% 3.43/1.63  tff(c_272, plain, (![C_140]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_140), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_140, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_140) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_126, c_126, c_264])).
% 3.43/1.63  tff(c_273, plain, (![C_140]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_140), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_140, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_140))), inference(negUnitSimplification, [status(thm)], [c_56, c_272])).
% 3.43/1.63  tff(c_281, plain, (![A_142, B_143, C_144]: (m1_subset_1(k3_filter_1(A_142, B_143, C_144), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_142, B_143), k8_eqrel_1(A_142, B_143)), k8_eqrel_1(A_142, B_143)))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_142, A_142), A_142))) | ~v1_funct_2(C_144, k2_zfmisc_1(A_142, A_142), A_142) | ~v1_funct_1(C_144) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_zfmisc_1(A_142, A_142))) | ~v8_relat_2(B_143) | ~v3_relat_2(B_143) | ~v1_partfun1(B_143, A_142) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.43/1.63  tff(c_296, plain, (![C_144]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_144), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_144, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_144) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_281])).
% 3.43/1.63  tff(c_309, plain, (![C_144]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_144), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_144, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_144) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_126, c_126, c_296])).
% 3.43/1.63  tff(c_317, plain, (![C_145]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_145), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_145, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_145))), inference(negUnitSimplification, [status(thm)], [c_56, c_309])).
% 3.43/1.63  tff(c_10, plain, (![A_11, B_12, C_14]: (r3_binop_1(A_11, B_12, C_14) | ~r2_binop_1(A_11, B_12, C_14) | ~r1_binop_1(A_11, B_12, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11, A_11), A_11))) | ~v1_funct_2(C_14, k2_zfmisc_1(A_11, A_11), A_11) | ~v1_funct_1(C_14) | ~m1_subset_1(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.43/1.63  tff(c_422, plain, (![B_168, C_169]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_168, k3_filter_1('#skF_1', '#skF_2', C_169)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_168, k3_filter_1('#skF_1', '#skF_2', C_169)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_168, k3_filter_1('#skF_1', '#skF_2', C_169)) | ~v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_169), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_169)) | ~m1_subset_1(B_168, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_169, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_169))), inference(resolution, [status(thm)], [c_317, c_10])).
% 3.43/1.63  tff(c_426, plain, (![B_170, C_171]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_170, k3_filter_1('#skF_1', '#skF_2', C_171)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_170, k3_filter_1('#skF_1', '#skF_2', C_171)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_170, k3_filter_1('#skF_1', '#skF_2', C_171)) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_171)) | ~m1_subset_1(B_170, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_171, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_171))), inference(resolution, [status(thm)], [c_273, c_422])).
% 3.43/1.63  tff(c_428, plain, (![B_170]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_170, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_170, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_170, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_170, k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_97, c_426])).
% 3.43/1.63  tff(c_432, plain, (![B_172]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_172, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_172, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_172, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_172, k7_eqrel_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_82, c_238, c_428])).
% 3.43/1.63  tff(c_40, plain, (~r3_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.43/1.63  tff(c_127, plain, (~r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_40])).
% 3.43/1.63  tff(c_446, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_432, c_127])).
% 3.43/1.63  tff(c_447, plain, (~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_446])).
% 3.43/1.63  tff(c_450, plain, (~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_184, c_447])).
% 3.43/1.63  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_450])).
% 3.43/1.63  tff(c_455, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_446])).
% 3.43/1.63  tff(c_476, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_455])).
% 3.43/1.63  tff(c_479, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_245, c_476])).
% 3.43/1.63  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_145, c_479])).
% 3.43/1.63  tff(c_484, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_455])).
% 3.43/1.63  tff(c_488, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_252, c_484])).
% 3.43/1.63  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_159, c_488])).
% 3.43/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.63  
% 3.43/1.63  Inference rules
% 3.43/1.63  ----------------------
% 3.43/1.63  #Ref     : 0
% 3.43/1.63  #Sup     : 77
% 3.43/1.63  #Fact    : 0
% 3.43/1.63  #Define  : 0
% 3.43/1.63  #Split   : 8
% 3.86/1.63  #Chain   : 0
% 3.86/1.63  #Close   : 0
% 3.86/1.63  
% 3.86/1.63  Ordering : KBO
% 3.86/1.63  
% 3.86/1.63  Simplification rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Subsume      : 18
% 3.86/1.63  #Demod        : 189
% 3.86/1.63  #Tautology    : 11
% 3.86/1.63  #SimpNegUnit  : 36
% 3.86/1.63  #BackRed      : 1
% 3.86/1.63  
% 3.86/1.63  #Partial instantiations: 0
% 3.86/1.63  #Strategies tried      : 1
% 3.86/1.63  
% 3.86/1.63  Timing (in seconds)
% 3.86/1.63  ----------------------
% 3.86/1.63  Preprocessing        : 0.41
% 3.86/1.63  Parsing              : 0.23
% 3.86/1.63  CNF conversion       : 0.03
% 3.86/1.63  Main loop            : 0.37
% 3.86/1.63  Inferencing          : 0.13
% 3.86/1.63  Reduction            : 0.12
% 3.86/1.63  Demodulation         : 0.09
% 3.86/1.63  BG Simplification    : 0.02
% 3.86/1.63  Subsumption          : 0.08
% 3.86/1.63  Abstraction          : 0.02
% 3.86/1.63  MUC search           : 0.00
% 3.86/1.63  Cooper               : 0.00
% 3.86/1.63  Total                : 0.84
% 3.86/1.63  Index Insertion      : 0.00
% 3.86/1.63  Index Deletion       : 0.00
% 3.86/1.63  Index Matching       : 0.00
% 3.86/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
