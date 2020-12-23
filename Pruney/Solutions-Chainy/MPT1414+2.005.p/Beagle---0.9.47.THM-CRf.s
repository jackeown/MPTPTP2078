%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:36 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  135 (1116 expanded)
%              Number of leaves         :   40 ( 433 expanded)
%              Depth                    :   16
%              Number of atoms          :  442 (4704 expanded)
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

tff(f_222,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_69,axiom,(
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

tff(f_155,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k8_eqrel_1(A,B) = k7_eqrel_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

tff(f_177,axiom,(
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

tff(f_199,axiom,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_subset_1(k7_eqrel_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

tff(f_145,axiom,(
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

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_92,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_46,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_66,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_73,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_funct_1(C_80)
      | ~ m2_filter_1(C_80,A_81,B_82)
      | ~ v1_relat_1(B_82)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_79,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_79])).

tff(c_81,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_funct_2(C_83,k2_zfmisc_1(A_84,A_84),A_84)
      | ~ m2_filter_1(C_83,A_84,B_85)
      | ~ v1_relat_1(B_85)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_83,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_86,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_83])).

tff(c_87,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_86])).

tff(c_96,plain,(
    ! [C_92,A_93,B_94] :
      ( m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_93,A_93),A_93)))
      | ~ m2_filter_1(C_92,A_93,B_94)
      | ~ v1_relat_1(B_94)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_98,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_101,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_98])).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_101])).

tff(c_44,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_170,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_binop_1(A_105,B_106,C_107)
      | ~ r3_binop_1(A_105,B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_105,A_105),A_105)))
      | ~ v1_funct_2(C_107,k2_zfmisc_1(A_105,A_105),A_105)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(B_106,A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_170])).

tff(c_175,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_87,c_102,c_172])).

tff(c_56,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_54,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_52,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_130,plain,(
    ! [A_97,B_98] :
      ( k8_eqrel_1(A_97,B_98) = k7_eqrel_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v1_partfun1(B_98,A_97)
      | ~ v8_relat_2(B_98)
      | ~ v3_relat_2(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_133,plain,
    ( k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_130])).

tff(c_136,plain,(
    k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_133])).

tff(c_273,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( r1_binop_1(k8_eqrel_1(A_134,B_135),k9_eqrel_1(A_134,B_135,C_136),k3_filter_1(A_134,B_135,D_137))
      | ~ r1_binop_1(A_134,C_136,D_137)
      | ~ m2_filter_1(D_137,A_134,B_135)
      | ~ m1_subset_1(C_136,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_134,A_134)))
      | ~ v8_relat_2(B_135)
      | ~ v3_relat_2(B_135)
      | ~ v1_partfun1(B_135,A_134)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_276,plain,(
    ! [C_136,D_137] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_136),k3_filter_1('#skF_1','#skF_2',D_137))
      | ~ r1_binop_1('#skF_1',C_136,D_137)
      | ~ m2_filter_1(D_137,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_136,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_273])).

tff(c_278,plain,(
    ! [C_136,D_137] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_136),k3_filter_1('#skF_1','#skF_2',D_137))
      | ~ r1_binop_1('#skF_1',C_136,D_137)
      | ~ m2_filter_1(D_137,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_136,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_276])).

tff(c_279,plain,(
    ! [C_136,D_137] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_136),k3_filter_1('#skF_1','#skF_2',D_137))
      | ~ r1_binop_1('#skF_1',C_136,D_137)
      | ~ m2_filter_1(D_137,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_136,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_278])).

tff(c_176,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_binop_1(A_108,B_109,C_110)
      | ~ r3_binop_1(A_108,B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_108,A_108),A_108)))
      | ~ v1_funct_2(C_110,k2_zfmisc_1(A_108,A_108),A_108)
      | ~ v1_funct_1(C_110)
      | ~ m1_subset_1(B_109,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_178,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_176])).

tff(c_181,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_87,c_102,c_178])).

tff(c_265,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( r2_binop_1(k8_eqrel_1(A_128,B_129),k9_eqrel_1(A_128,B_129,C_130),k3_filter_1(A_128,B_129,D_131))
      | ~ r2_binop_1(A_128,C_130,D_131)
      | ~ m2_filter_1(D_131,A_128,B_129)
      | ~ m1_subset_1(C_130,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v8_relat_2(B_129)
      | ~ v3_relat_2(B_129)
      | ~ v1_partfun1(B_129,A_128)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_268,plain,(
    ! [C_130,D_131] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_130),k3_filter_1('#skF_1','#skF_2',D_131))
      | ~ r2_binop_1('#skF_1',C_130,D_131)
      | ~ m2_filter_1(D_131,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_130,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_265])).

tff(c_270,plain,(
    ! [C_130,D_131] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_130),k3_filter_1('#skF_1','#skF_2',D_131))
      | ~ r2_binop_1('#skF_1',C_130,D_131)
      | ~ m2_filter_1(D_131,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_130,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_268])).

tff(c_271,plain,(
    ! [C_130,D_131] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_130),k3_filter_1('#skF_1','#skF_2',D_131))
      | ~ r2_binop_1('#skF_1',C_130,D_131)
      | ~ m2_filter_1(D_131,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_130,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_270])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k7_eqrel_1(A_20,B_21),k1_zfmisc_1(k1_zfmisc_1(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v1_partfun1(B_21,A_20)
      | ~ v8_relat_2(B_21)
      | ~ v3_relat_2(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_116,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(k7_eqrel_1(A_95,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v1_partfun1(B_96,A_95)
      | ~ v8_relat_2(B_96)
      | ~ v3_relat_2(B_96)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_119,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_122,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_119])).

tff(c_123,plain,(
    ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_122])).

tff(c_142,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k7_eqrel_1(A_99,B_100),k1_zfmisc_1(k1_zfmisc_1(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v1_partfun1(B_100,A_99)
      | ~ v8_relat_2(B_100)
      | ~ v3_relat_2(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_103,B_104] :
      ( v1_xboole_0(k7_eqrel_1(A_103,B_104))
      | ~ v1_xboole_0(k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v1_partfun1(B_104,A_103)
      | ~ v8_relat_2(B_104)
      | ~ v3_relat_2(B_104) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_165,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_162])).

tff(c_168,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_165])).

tff(c_169,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_168])).

tff(c_182,plain,(
    ! [A_111,B_112,C_113] :
      ( m2_subset_1(k9_eqrel_1(A_111,B_112,C_113),k1_zfmisc_1(A_111),k8_eqrel_1(A_111,B_112))
      | ~ m1_subset_1(C_113,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_111,A_111)))
      | ~ v1_partfun1(B_112,A_111)
      | ~ v8_relat_2(B_112)
      | ~ v3_relat_2(B_112)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_187,plain,(
    ! [C_113] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_113),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_113,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_partfun1('#skF_2','#skF_1')
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_182])).

tff(c_190,plain,(
    ! [C_113] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_113),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_113,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_50,c_187])).

tff(c_192,plain,(
    ! [C_114] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_114),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_114,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_190])).

tff(c_8,plain,(
    ! [C_12,B_10,A_9] :
      ( m1_subset_1(C_12,B_10)
      | ~ m2_subset_1(C_12,A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9))
      | v1_xboole_0(B_10)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_194,plain,(
    ! [C_114] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_114),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_114,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_197,plain,(
    ! [C_114] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_114),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(C_114,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_123,c_194])).

tff(c_198,plain,(
    ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_201,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_50,c_201])).

tff(c_206,plain,(
    ! [C_114] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_114),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_114,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_251,plain,(
    ! [A_124,B_125,C_126] :
      ( v1_funct_1(k3_filter_1(A_124,B_125,C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_124,A_124),A_124)))
      | ~ v1_funct_2(C_126,k2_zfmisc_1(A_124,A_124),A_124)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1(A_124,A_124)))
      | ~ v8_relat_2(B_125)
      | ~ v3_relat_2(B_125)
      | ~ v1_partfun1(B_125,A_124)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_253,plain,(
    ! [B_125] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_125,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_125)
      | ~ v3_relat_2(B_125)
      | ~ v1_partfun1(B_125,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_102,c_251])).

tff(c_256,plain,(
    ! [B_125] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_125,'#skF_4'))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_125)
      | ~ v3_relat_2(B_125)
      | ~ v1_partfun1(B_125,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_87,c_253])).

tff(c_258,plain,(
    ! [B_127] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_127,'#skF_4'))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_127)
      | ~ v3_relat_2(B_127)
      | ~ v1_partfun1(B_127,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_256])).

tff(c_261,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_258])).

tff(c_264,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_261])).

tff(c_280,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_283,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_136,c_280])).

tff(c_291,plain,(
    ! [C_140] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_140),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_140,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_136,c_136,c_283])).

tff(c_292,plain,(
    ! [C_140] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_140),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_140,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_291])).

tff(c_307,plain,(
    ! [A_147,B_148,C_149] :
      ( m1_subset_1(k3_filter_1(A_147,B_148,C_149),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_147,B_148),k8_eqrel_1(A_147,B_148)),k8_eqrel_1(A_147,B_148))))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_147,A_147),A_147)))
      | ~ v1_funct_2(C_149,k2_zfmisc_1(A_147,A_147),A_147)
      | ~ v1_funct_1(C_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_zfmisc_1(A_147,A_147)))
      | ~ v8_relat_2(B_148)
      | ~ v3_relat_2(B_148)
      | ~ v1_partfun1(B_148,A_147)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_322,plain,(
    ! [C_149] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_149),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_149,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_149)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_307])).

tff(c_337,plain,(
    ! [C_149] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_149),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_149,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_149)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_136,c_136,c_322])).

tff(c_345,plain,(
    ! [C_150] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_150),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_150,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_337])).

tff(c_12,plain,(
    ! [A_13,B_14,C_16] :
      ( r3_binop_1(A_13,B_14,C_16)
      | ~ r2_binop_1(A_13,B_14,C_16)
      | ~ r1_binop_1(A_13,B_14,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(C_16,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(B_14,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_452,plain,(
    ! [B_173,C_174] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_174),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ m1_subset_1(B_173,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_174,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_345,c_12])).

tff(c_456,plain,(
    ! [B_175,C_176] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_175,k3_filter_1('#skF_1','#skF_2',C_176))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_175,k3_filter_1('#skF_1','#skF_2',C_176))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_175,k3_filter_1('#skF_1','#skF_2',C_176))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_176))
      | ~ m1_subset_1(B_175,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_176,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_292,c_452])).

tff(c_458,plain,(
    ! [B_175] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_175,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_175,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_175,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_175,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_456])).

tff(c_462,plain,(
    ! [B_177] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_177,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_177,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_177,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_177,k7_eqrel_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_87,c_264,c_458])).

tff(c_42,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_137,plain,(
    ~ r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_42])).

tff(c_476,plain,
    ( ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_462,c_137])).

tff(c_477,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_480,plain,(
    ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_477])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_480])).

tff(c_485,plain,
    ( ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_487,plain,(
    ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_509,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_271,c_487])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_181,c_509])).

tff(c_514,plain,(
    ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_518,plain,
    ( ~ r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_279,c_514])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_175,c_518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.56  
% 3.35/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.56  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.35/1.56  
% 3.35/1.56  %Foreground sorts:
% 3.35/1.56  
% 3.35/1.56  
% 3.35/1.56  %Background operators:
% 3.35/1.56  
% 3.35/1.56  
% 3.35/1.56  %Foreground operators:
% 3.35/1.56  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 3.35/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.56  tff(k7_eqrel_1, type, k7_eqrel_1: ($i * $i) > $i).
% 3.35/1.56  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.35/1.56  tff(k9_eqrel_1, type, k9_eqrel_1: ($i * $i * $i) > $i).
% 3.35/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.56  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 3.35/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.56  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.35/1.56  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 3.35/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.56  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 3.35/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.56  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 3.35/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.56  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 3.35/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.56  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 3.35/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.56  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 3.35/1.56  
% 3.35/1.59  tff(f_222, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r3_binop_1(A, C, D) => r3_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_filter_1)).
% 3.35/1.59  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.35/1.59  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.35/1.59  tff(f_131, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.35/1.59  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_binop_1)).
% 3.35/1.59  tff(f_155, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k8_eqrel_1(A, B) = k7_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_eqrel_1)).
% 3.35/1.59  tff(f_177, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r1_binop_1(A, C, D) => r1_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_filter_1)).
% 3.35/1.59  tff(f_199, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r2_binop_1(A, C, D) => r2_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_filter_1)).
% 3.35/1.59  tff(f_102, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => m1_subset_1(k7_eqrel_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_eqrel_1)).
% 3.35/1.59  tff(f_145, axiom, (![A, B]: (((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ~v1_xboole_0(k7_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_eqrel_1)).
% 3.35/1.59  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.35/1.59  tff(f_117, axiom, (![A, B, C]: ((((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & m1_subset_1(C, A)) => m2_subset_1(k9_eqrel_1(A, B, C), k1_zfmisc_1(A), k8_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 3.35/1.59  tff(f_54, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 3.35/1.59  tff(f_92, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.35/1.59  tff(c_48, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_46, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_58, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.59  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_66, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.59  tff(c_69, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 3.35/1.59  tff(c_72, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 3.35/1.59  tff(c_73, plain, (![C_80, A_81, B_82]: (v1_funct_1(C_80) | ~m2_filter_1(C_80, A_81, B_82) | ~v1_relat_1(B_82) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.59  tff(c_76, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_73])).
% 3.35/1.59  tff(c_79, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76])).
% 3.35/1.59  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_79])).
% 3.35/1.59  tff(c_81, plain, (![C_83, A_84, B_85]: (v1_funct_2(C_83, k2_zfmisc_1(A_84, A_84), A_84) | ~m2_filter_1(C_83, A_84, B_85) | ~v1_relat_1(B_85) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.59  tff(c_83, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_81])).
% 3.35/1.59  tff(c_86, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_83])).
% 3.35/1.59  tff(c_87, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_86])).
% 3.35/1.59  tff(c_96, plain, (![C_92, A_93, B_94]: (m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_93, A_93), A_93))) | ~m2_filter_1(C_92, A_93, B_94) | ~v1_relat_1(B_94) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.59  tff(c_98, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_96])).
% 3.35/1.59  tff(c_101, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_98])).
% 3.35/1.59  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_101])).
% 3.35/1.59  tff(c_44, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_170, plain, (![A_105, B_106, C_107]: (r1_binop_1(A_105, B_106, C_107) | ~r3_binop_1(A_105, B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_105, A_105), A_105))) | ~v1_funct_2(C_107, k2_zfmisc_1(A_105, A_105), A_105) | ~v1_funct_1(C_107) | ~m1_subset_1(B_106, A_105))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.35/1.59  tff(c_172, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_170])).
% 3.35/1.59  tff(c_175, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_87, c_102, c_172])).
% 3.35/1.59  tff(c_56, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_54, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_52, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_130, plain, (![A_97, B_98]: (k8_eqrel_1(A_97, B_98)=k7_eqrel_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v1_partfun1(B_98, A_97) | ~v8_relat_2(B_98) | ~v3_relat_2(B_98))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.35/1.59  tff(c_133, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_130])).
% 3.35/1.59  tff(c_136, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_133])).
% 3.35/1.59  tff(c_273, plain, (![A_134, B_135, C_136, D_137]: (r1_binop_1(k8_eqrel_1(A_134, B_135), k9_eqrel_1(A_134, B_135, C_136), k3_filter_1(A_134, B_135, D_137)) | ~r1_binop_1(A_134, C_136, D_137) | ~m2_filter_1(D_137, A_134, B_135) | ~m1_subset_1(C_136, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_134, A_134))) | ~v8_relat_2(B_135) | ~v3_relat_2(B_135) | ~v1_partfun1(B_135, A_134) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.35/1.59  tff(c_276, plain, (![C_136, D_137]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_136), k3_filter_1('#skF_1', '#skF_2', D_137)) | ~r1_binop_1('#skF_1', C_136, D_137) | ~m2_filter_1(D_137, '#skF_1', '#skF_2') | ~m1_subset_1(C_136, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_273])).
% 3.35/1.59  tff(c_278, plain, (![C_136, D_137]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_136), k3_filter_1('#skF_1', '#skF_2', D_137)) | ~r1_binop_1('#skF_1', C_136, D_137) | ~m2_filter_1(D_137, '#skF_1', '#skF_2') | ~m1_subset_1(C_136, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_276])).
% 3.35/1.59  tff(c_279, plain, (![C_136, D_137]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_136), k3_filter_1('#skF_1', '#skF_2', D_137)) | ~r1_binop_1('#skF_1', C_136, D_137) | ~m2_filter_1(D_137, '#skF_1', '#skF_2') | ~m1_subset_1(C_136, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_278])).
% 3.35/1.59  tff(c_176, plain, (![A_108, B_109, C_110]: (r2_binop_1(A_108, B_109, C_110) | ~r3_binop_1(A_108, B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_108, A_108), A_108))) | ~v1_funct_2(C_110, k2_zfmisc_1(A_108, A_108), A_108) | ~v1_funct_1(C_110) | ~m1_subset_1(B_109, A_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.35/1.59  tff(c_178, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_176])).
% 3.35/1.59  tff(c_181, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_87, c_102, c_178])).
% 3.35/1.59  tff(c_265, plain, (![A_128, B_129, C_130, D_131]: (r2_binop_1(k8_eqrel_1(A_128, B_129), k9_eqrel_1(A_128, B_129, C_130), k3_filter_1(A_128, B_129, D_131)) | ~r2_binop_1(A_128, C_130, D_131) | ~m2_filter_1(D_131, A_128, B_129) | ~m1_subset_1(C_130, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1(A_128, A_128))) | ~v8_relat_2(B_129) | ~v3_relat_2(B_129) | ~v1_partfun1(B_129, A_128) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.35/1.59  tff(c_268, plain, (![C_130, D_131]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_130), k3_filter_1('#skF_1', '#skF_2', D_131)) | ~r2_binop_1('#skF_1', C_130, D_131) | ~m2_filter_1(D_131, '#skF_1', '#skF_2') | ~m1_subset_1(C_130, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_265])).
% 3.35/1.59  tff(c_270, plain, (![C_130, D_131]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_130), k3_filter_1('#skF_1', '#skF_2', D_131)) | ~r2_binop_1('#skF_1', C_130, D_131) | ~m2_filter_1(D_131, '#skF_1', '#skF_2') | ~m1_subset_1(C_130, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_268])).
% 3.35/1.59  tff(c_271, plain, (![C_130, D_131]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_130), k3_filter_1('#skF_1', '#skF_2', D_131)) | ~r2_binop_1('#skF_1', C_130, D_131) | ~m2_filter_1(D_131, '#skF_1', '#skF_2') | ~m1_subset_1(C_130, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_270])).
% 3.35/1.59  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(k7_eqrel_1(A_20, B_21), k1_zfmisc_1(k1_zfmisc_1(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v1_partfun1(B_21, A_20) | ~v8_relat_2(B_21) | ~v3_relat_2(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.35/1.59  tff(c_116, plain, (![A_95, B_96]: (~v1_xboole_0(k7_eqrel_1(A_95, B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v1_partfun1(B_96, A_95) | ~v8_relat_2(B_96) | ~v3_relat_2(B_96) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.35/1.59  tff(c_119, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_116])).
% 3.35/1.59  tff(c_122, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_119])).
% 3.35/1.59  tff(c_123, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_122])).
% 3.35/1.59  tff(c_142, plain, (![A_99, B_100]: (m1_subset_1(k7_eqrel_1(A_99, B_100), k1_zfmisc_1(k1_zfmisc_1(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v1_partfun1(B_100, A_99) | ~v8_relat_2(B_100) | ~v3_relat_2(B_100))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.35/1.59  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.59  tff(c_162, plain, (![A_103, B_104]: (v1_xboole_0(k7_eqrel_1(A_103, B_104)) | ~v1_xboole_0(k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v1_partfun1(B_104, A_103) | ~v8_relat_2(B_104) | ~v3_relat_2(B_104))), inference(resolution, [status(thm)], [c_142, c_2])).
% 3.35/1.59  tff(c_165, plain, (v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_162])).
% 3.35/1.59  tff(c_168, plain, (v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_165])).
% 3.35/1.59  tff(c_169, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_123, c_168])).
% 3.35/1.59  tff(c_182, plain, (![A_111, B_112, C_113]: (m2_subset_1(k9_eqrel_1(A_111, B_112, C_113), k1_zfmisc_1(A_111), k8_eqrel_1(A_111, B_112)) | ~m1_subset_1(C_113, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(A_111, A_111))) | ~v1_partfun1(B_112, A_111) | ~v8_relat_2(B_112) | ~v3_relat_2(B_112) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.35/1.59  tff(c_187, plain, (![C_113]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_113), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_113, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_182])).
% 3.35/1.59  tff(c_190, plain, (![C_113]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_113), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_113, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_50, c_187])).
% 3.35/1.59  tff(c_192, plain, (![C_114]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_114), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_114, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_190])).
% 3.35/1.59  tff(c_8, plain, (![C_12, B_10, A_9]: (m1_subset_1(C_12, B_10) | ~m2_subset_1(C_12, A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)) | v1_xboole_0(B_10) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.35/1.59  tff(c_194, plain, (![C_114]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_114), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_114, '#skF_1'))), inference(resolution, [status(thm)], [c_192, c_8])).
% 3.35/1.59  tff(c_197, plain, (![C_114]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_114), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1(C_114, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_169, c_123, c_194])).
% 3.35/1.59  tff(c_198, plain, (~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_197])).
% 3.35/1.59  tff(c_201, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_24, c_198])).
% 3.35/1.59  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_50, c_201])).
% 3.35/1.59  tff(c_206, plain, (![C_114]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_114), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_114, '#skF_1'))), inference(splitRight, [status(thm)], [c_197])).
% 3.35/1.59  tff(c_251, plain, (![A_124, B_125, C_126]: (v1_funct_1(k3_filter_1(A_124, B_125, C_126)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_124, A_124), A_124))) | ~v1_funct_2(C_126, k2_zfmisc_1(A_124, A_124), A_124) | ~v1_funct_1(C_126) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1(A_124, A_124))) | ~v8_relat_2(B_125) | ~v3_relat_2(B_125) | ~v1_partfun1(B_125, A_124) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.35/1.59  tff(c_253, plain, (![B_125]: (v1_funct_1(k3_filter_1('#skF_1', B_125, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_125) | ~v3_relat_2(B_125) | ~v1_partfun1(B_125, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_251])).
% 3.35/1.59  tff(c_256, plain, (![B_125]: (v1_funct_1(k3_filter_1('#skF_1', B_125, '#skF_4')) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_125) | ~v3_relat_2(B_125) | ~v1_partfun1(B_125, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_87, c_253])).
% 3.35/1.59  tff(c_258, plain, (![B_127]: (v1_funct_1(k3_filter_1('#skF_1', B_127, '#skF_4')) | ~m1_subset_1(B_127, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_127) | ~v3_relat_2(B_127) | ~v1_partfun1(B_127, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_256])).
% 3.35/1.59  tff(c_261, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_258])).
% 3.35/1.59  tff(c_264, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_261])).
% 3.35/1.59  tff(c_280, plain, (![A_138, B_139, C_140]: (v1_funct_2(k3_filter_1(A_138, B_139, C_140), k2_zfmisc_1(k8_eqrel_1(A_138, B_139), k8_eqrel_1(A_138, B_139)), k8_eqrel_1(A_138, B_139)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_138, A_138), A_138))) | ~v1_funct_2(C_140, k2_zfmisc_1(A_138, A_138), A_138) | ~v1_funct_1(C_140) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v8_relat_2(B_139) | ~v3_relat_2(B_139) | ~v1_partfun1(B_139, A_138) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.35/1.59  tff(c_283, plain, (![C_140]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_140), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_140, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_140) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_280])).
% 3.35/1.59  tff(c_291, plain, (![C_140]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_140), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_140, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_140) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_136, c_136, c_283])).
% 3.35/1.59  tff(c_292, plain, (![C_140]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_140), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_140, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_140))), inference(negUnitSimplification, [status(thm)], [c_58, c_291])).
% 3.35/1.59  tff(c_307, plain, (![A_147, B_148, C_149]: (m1_subset_1(k3_filter_1(A_147, B_148, C_149), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_147, B_148), k8_eqrel_1(A_147, B_148)), k8_eqrel_1(A_147, B_148)))) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_147, A_147), A_147))) | ~v1_funct_2(C_149, k2_zfmisc_1(A_147, A_147), A_147) | ~v1_funct_1(C_149) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_zfmisc_1(A_147, A_147))) | ~v8_relat_2(B_148) | ~v3_relat_2(B_148) | ~v1_partfun1(B_148, A_147) | v1_xboole_0(A_147))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.35/1.59  tff(c_322, plain, (![C_149]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_149), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_149, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_149) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_307])).
% 3.35/1.59  tff(c_337, plain, (![C_149]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_149), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_149, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_149) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_136, c_136, c_322])).
% 3.35/1.59  tff(c_345, plain, (![C_150]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_150), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_150, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_150))), inference(negUnitSimplification, [status(thm)], [c_58, c_337])).
% 3.35/1.59  tff(c_12, plain, (![A_13, B_14, C_16]: (r3_binop_1(A_13, B_14, C_16) | ~r2_binop_1(A_13, B_14, C_16) | ~r1_binop_1(A_13, B_14, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13, A_13), A_13))) | ~v1_funct_2(C_16, k2_zfmisc_1(A_13, A_13), A_13) | ~v1_funct_1(C_16) | ~m1_subset_1(B_14, A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.35/1.59  tff(c_452, plain, (![B_173, C_174]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', C_174)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', C_174)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', C_174)) | ~v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_174), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_174)) | ~m1_subset_1(B_173, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_174, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_174))), inference(resolution, [status(thm)], [c_345, c_12])).
% 3.35/1.59  tff(c_456, plain, (![B_175, C_176]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_175, k3_filter_1('#skF_1', '#skF_2', C_176)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_175, k3_filter_1('#skF_1', '#skF_2', C_176)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_175, k3_filter_1('#skF_1', '#skF_2', C_176)) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_176)) | ~m1_subset_1(B_175, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_176, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_176))), inference(resolution, [status(thm)], [c_292, c_452])).
% 3.35/1.59  tff(c_458, plain, (![B_175]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_175, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_175, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_175, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_175, k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_456])).
% 3.35/1.59  tff(c_462, plain, (![B_177]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_177, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_177, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_177, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_177, k7_eqrel_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_87, c_264, c_458])).
% 3.35/1.59  tff(c_42, plain, (~r3_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 3.35/1.59  tff(c_137, plain, (~r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_42])).
% 3.35/1.59  tff(c_476, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_462, c_137])).
% 3.35/1.59  tff(c_477, plain, (~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_476])).
% 3.35/1.59  tff(c_480, plain, (~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_206, c_477])).
% 3.35/1.59  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_480])).
% 3.35/1.59  tff(c_485, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_476])).
% 3.35/1.59  tff(c_487, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_485])).
% 3.35/1.59  tff(c_509, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_271, c_487])).
% 3.35/1.59  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_181, c_509])).
% 3.35/1.59  tff(c_514, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_485])).
% 3.35/1.59  tff(c_518, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_279, c_514])).
% 3.35/1.59  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_175, c_518])).
% 3.35/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.59  
% 3.35/1.59  Inference rules
% 3.35/1.59  ----------------------
% 3.35/1.59  #Ref     : 0
% 3.35/1.59  #Sup     : 80
% 3.35/1.59  #Fact    : 0
% 3.35/1.59  #Define  : 0
% 3.35/1.59  #Split   : 10
% 3.35/1.59  #Chain   : 0
% 3.35/1.59  #Close   : 0
% 3.35/1.59  
% 3.35/1.59  Ordering : KBO
% 3.35/1.59  
% 3.35/1.59  Simplification rules
% 3.35/1.59  ----------------------
% 3.35/1.59  #Subsume      : 20
% 3.35/1.59  #Demod        : 196
% 3.35/1.59  #Tautology    : 11
% 3.35/1.59  #SimpNegUnit  : 36
% 3.35/1.59  #BackRed      : 1
% 3.35/1.59  
% 3.35/1.59  #Partial instantiations: 0
% 3.35/1.59  #Strategies tried      : 1
% 3.35/1.59  
% 3.35/1.59  Timing (in seconds)
% 3.35/1.59  ----------------------
% 3.35/1.59  Preprocessing        : 0.37
% 3.35/1.59  Parsing              : 0.20
% 3.35/1.59  CNF conversion       : 0.03
% 3.35/1.59  Main loop            : 0.38
% 3.35/1.59  Inferencing          : 0.14
% 3.35/1.59  Reduction            : 0.13
% 3.35/1.59  Demodulation         : 0.09
% 3.35/1.59  BG Simplification    : 0.02
% 3.35/1.59  Subsumption          : 0.08
% 3.35/1.59  Abstraction          : 0.02
% 3.35/1.59  MUC search           : 0.00
% 3.35/1.59  Cooper               : 0.00
% 3.35/1.59  Total                : 0.80
% 3.35/1.59  Index Insertion      : 0.00
% 3.35/1.59  Index Deletion       : 0.00
% 3.35/1.60  Index Matching       : 0.00
% 3.35/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
