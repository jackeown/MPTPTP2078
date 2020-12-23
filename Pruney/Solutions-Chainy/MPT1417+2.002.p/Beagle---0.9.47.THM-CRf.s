%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:37 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 813 expanded)
%              Number of leaves         :   31 ( 305 expanded)
%              Depth                    :   16
%              Number of atoms          :  370 (3180 expanded)
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

tff(f_157,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_53,axiom,(
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

tff(f_112,axiom,(
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

tff(f_134,axiom,(
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

tff(f_76,axiom,(
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

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_38,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_34,plain,(
    m2_filter_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_53,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_funct_1(C_62)
      | ~ m2_filter_1(C_62,A_63,B_64)
      | ~ v1_relat_1(B_64)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,
    ( v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_62,plain,
    ( v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56])).

tff(c_63,plain,(
    v1_funct_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_62])).

tff(c_68,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_funct_2(C_65,k2_zfmisc_1(A_66,A_66),A_66)
      | ~ m2_filter_1(C_65,A_66,B_67)
      | ~ v1_relat_1(B_67)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,
    ( v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_75,plain,
    ( v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_75])).

tff(c_81,plain,(
    ! [C_68,A_69,B_70] :
      ( m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_69,A_69),A_69)))
      | ~ m2_filter_1(C_68,A_69,B_70)
      | ~ v1_relat_1(B_70)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_83,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_88,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_89,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_88])).

tff(c_59,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_66,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_59])).

tff(c_67,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_66])).

tff(c_72,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_79,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72])).

tff(c_80,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_79])).

tff(c_85,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_92,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_93,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_92])).

tff(c_30,plain,(
    r6_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_135,plain,(
    ! [A_84,B_85,C_86] :
      ( r5_binop_1(A_84,B_85,C_86)
      | ~ r6_binop_1(A_84,B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84,A_84),A_84)))
      | ~ v1_funct_2(C_86,k2_zfmisc_1(A_84,A_84),A_84)
      | ~ v1_funct_1(C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84,A_84),A_84)))
      | ~ v1_funct_2(B_85,k2_zfmisc_1(A_84,A_84),A_84)
      | ~ v1_funct_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,
    ( r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_140,plain,(
    r5_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_76,c_89,c_67,c_80,c_93,c_137])).

tff(c_24,plain,(
    ! [A_17,B_25,C_29,D_31] :
      ( r5_binop_1(k8_eqrel_1(A_17,B_25),k3_filter_1(A_17,B_25,C_29),k3_filter_1(A_17,B_25,D_31))
      | ~ r5_binop_1(A_17,C_29,D_31)
      | ~ m2_filter_1(D_31,A_17,B_25)
      | ~ m2_filter_1(C_29,A_17,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v8_relat_2(B_25)
      | ~ v3_relat_2(B_25)
      | ~ v1_partfun1(B_25,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_141,plain,(
    ! [A_87,B_88,C_89] :
      ( r4_binop_1(A_87,B_88,C_89)
      | ~ r6_binop_1(A_87,B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_87,A_87),A_87)))
      | ~ v1_funct_2(C_89,k2_zfmisc_1(A_87,A_87),A_87)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_87,A_87),A_87)))
      | ~ v1_funct_2(B_88,k2_zfmisc_1(A_87,A_87),A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,
    ( r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_146,plain,(
    r4_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_76,c_89,c_67,c_80,c_93,c_143])).

tff(c_26,plain,(
    ! [A_32,B_40,C_44,D_46] :
      ( r4_binop_1(k8_eqrel_1(A_32,B_40),k3_filter_1(A_32,B_40,C_44),k3_filter_1(A_32,B_40,D_46))
      | ~ r4_binop_1(A_32,C_44,D_46)
      | ~ m2_filter_1(D_46,A_32,B_40)
      | ~ m2_filter_1(C_44,A_32,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v8_relat_2(B_40)
      | ~ v3_relat_2(B_40)
      | ~ v1_partfun1(B_40,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_106,plain,(
    ! [A_71,B_72,C_73] :
      ( v1_funct_1(k3_filter_1(A_71,B_72,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_71,A_71),A_71)))
      | ~ v1_funct_2(C_73,k2_zfmisc_1(A_71,A_71),A_71)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1(A_71,A_71)))
      | ~ v8_relat_2(B_72)
      | ~ v3_relat_2(B_72)
      | ~ v1_partfun1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    ! [B_72] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_72,'#skF_3'))
      | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_72)
      | ~ v3_relat_2(B_72)
      | ~ v1_partfun1(B_72,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_89,c_106])).

tff(c_117,plain,(
    ! [B_72] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_72,'#skF_3'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_72)
      | ~ v3_relat_2(B_72)
      | ~ v1_partfun1(B_72,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_76,c_110])).

tff(c_127,plain,(
    ! [B_79] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_79,'#skF_3'))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_79)
      | ~ v3_relat_2(B_79)
      | ~ v1_partfun1(B_79,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_117])).

tff(c_130,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_3'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_127])).

tff(c_133,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_130])).

tff(c_108,plain,(
    ! [B_72] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_72,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_72)
      | ~ v3_relat_2(B_72)
      | ~ v1_partfun1(B_72,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_93,c_106])).

tff(c_113,plain,(
    ! [B_72] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_72,'#skF_4'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_72)
      | ~ v3_relat_2(B_72)
      | ~ v1_partfun1(B_72,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_80,c_108])).

tff(c_119,plain,(
    ! [B_74] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_74,'#skF_4'))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_74)
      | ~ v3_relat_2(B_74)
      | ~ v1_partfun1(B_74,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_113])).

tff(c_122,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_119])).

tff(c_125,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_122])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( v1_funct_2(k3_filter_1(A_10,B_11,C_12),k2_zfmisc_1(k8_eqrel_1(A_10,B_11),k8_eqrel_1(A_10,B_11)),k8_eqrel_1(A_10,B_11))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_10,A_10),A_10)))
      | ~ v1_funct_2(C_12,k2_zfmisc_1(A_10,A_10),A_10)
      | ~ v1_funct_1(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k2_zfmisc_1(A_10,A_10)))
      | ~ v8_relat_2(B_11)
      | ~ v3_relat_2(B_11)
      | ~ v1_partfun1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k3_filter_1(A_10,B_11,C_12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_10,B_11),k8_eqrel_1(A_10,B_11)),k8_eqrel_1(A_10,B_11))))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_10,A_10),A_10)))
      | ~ v1_funct_2(C_12,k2_zfmisc_1(A_10,A_10),A_10)
      | ~ v1_funct_1(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k2_zfmisc_1(A_10,A_10)))
      | ~ v8_relat_2(B_11)
      | ~ v3_relat_2(B_11)
      | ~ v1_partfun1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_188,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k3_filter_1(A_98,B_99,C_100),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_98,B_99),k8_eqrel_1(A_98,B_99)),k8_eqrel_1(A_98,B_99))))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_98,A_98),A_98)))
      | ~ v1_funct_2(C_100,k2_zfmisc_1(A_98,A_98),A_98)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v8_relat_2(B_99)
      | ~ v3_relat_2(B_99)
      | ~ v1_partfun1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_6,B_7,C_9] :
      ( r6_binop_1(A_6,B_7,C_9)
      | ~ r5_binop_1(A_6,B_7,C_9)
      | ~ r4_binop_1(A_6,B_7,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_6,A_6),A_6)))
      | ~ v1_funct_2(C_9,k2_zfmisc_1(A_6,A_6),A_6)
      | ~ v1_funct_1(C_9)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_6,A_6),A_6)))
      | ~ v1_funct_2(B_7,k2_zfmisc_1(A_6,A_6),A_6)
      | ~ v1_funct_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_241,plain,(
    ! [A_122,B_123,B_124,C_125] :
      ( r6_binop_1(k8_eqrel_1(A_122,B_123),B_124,k3_filter_1(A_122,B_123,C_125))
      | ~ r5_binop_1(k8_eqrel_1(A_122,B_123),B_124,k3_filter_1(A_122,B_123,C_125))
      | ~ r4_binop_1(k8_eqrel_1(A_122,B_123),B_124,k3_filter_1(A_122,B_123,C_125))
      | ~ v1_funct_2(k3_filter_1(A_122,B_123,C_125),k2_zfmisc_1(k8_eqrel_1(A_122,B_123),k8_eqrel_1(A_122,B_123)),k8_eqrel_1(A_122,B_123))
      | ~ v1_funct_1(k3_filter_1(A_122,B_123,C_125))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_122,B_123),k8_eqrel_1(A_122,B_123)),k8_eqrel_1(A_122,B_123))))
      | ~ v1_funct_2(B_124,k2_zfmisc_1(k8_eqrel_1(A_122,B_123),k8_eqrel_1(A_122,B_123)),k8_eqrel_1(A_122,B_123))
      | ~ v1_funct_1(B_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_122,A_122),A_122)))
      | ~ v1_funct_2(C_125,k2_zfmisc_1(A_122,A_122),A_122)
      | ~ v1_funct_1(C_125)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_zfmisc_1(A_122,A_122)))
      | ~ v8_relat_2(B_123)
      | ~ v3_relat_2(B_123)
      | ~ v1_partfun1(B_123,A_122)
      | v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_188,c_6])).

tff(c_245,plain,(
    ! [A_126,B_127,B_128,C_129] :
      ( r6_binop_1(k8_eqrel_1(A_126,B_127),B_128,k3_filter_1(A_126,B_127,C_129))
      | ~ r5_binop_1(k8_eqrel_1(A_126,B_127),B_128,k3_filter_1(A_126,B_127,C_129))
      | ~ r4_binop_1(k8_eqrel_1(A_126,B_127),B_128,k3_filter_1(A_126,B_127,C_129))
      | ~ v1_funct_1(k3_filter_1(A_126,B_127,C_129))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_126,B_127),k8_eqrel_1(A_126,B_127)),k8_eqrel_1(A_126,B_127))))
      | ~ v1_funct_2(B_128,k2_zfmisc_1(k8_eqrel_1(A_126,B_127),k8_eqrel_1(A_126,B_127)),k8_eqrel_1(A_126,B_127))
      | ~ v1_funct_1(B_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_126,A_126),A_126)))
      | ~ v1_funct_2(C_129,k2_zfmisc_1(A_126,A_126),A_126)
      | ~ v1_funct_1(C_129)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1(A_126,A_126)))
      | ~ v8_relat_2(B_127)
      | ~ v3_relat_2(B_127)
      | ~ v1_partfun1(B_127,A_126)
      | v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_14,c_241])).

tff(c_249,plain,(
    ! [A_130,B_131,C_132,C_133] :
      ( r6_binop_1(k8_eqrel_1(A_130,B_131),k3_filter_1(A_130,B_131,C_132),k3_filter_1(A_130,B_131,C_133))
      | ~ r5_binop_1(k8_eqrel_1(A_130,B_131),k3_filter_1(A_130,B_131,C_132),k3_filter_1(A_130,B_131,C_133))
      | ~ r4_binop_1(k8_eqrel_1(A_130,B_131),k3_filter_1(A_130,B_131,C_132),k3_filter_1(A_130,B_131,C_133))
      | ~ v1_funct_1(k3_filter_1(A_130,B_131,C_133))
      | ~ v1_funct_2(k3_filter_1(A_130,B_131,C_132),k2_zfmisc_1(k8_eqrel_1(A_130,B_131),k8_eqrel_1(A_130,B_131)),k8_eqrel_1(A_130,B_131))
      | ~ v1_funct_1(k3_filter_1(A_130,B_131,C_132))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_130,A_130),A_130)))
      | ~ v1_funct_2(C_133,k2_zfmisc_1(A_130,A_130),A_130)
      | ~ v1_funct_1(C_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_130,A_130),A_130)))
      | ~ v1_funct_2(C_132,k2_zfmisc_1(A_130,A_130),A_130)
      | ~ v1_funct_1(C_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_zfmisc_1(A_130,A_130)))
      | ~ v8_relat_2(B_131)
      | ~ v3_relat_2(B_131)
      | ~ v1_partfun1(B_131,A_130)
      | v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_12,c_245])).

tff(c_253,plain,(
    ! [A_134,B_135,C_136,C_137] :
      ( r6_binop_1(k8_eqrel_1(A_134,B_135),k3_filter_1(A_134,B_135,C_136),k3_filter_1(A_134,B_135,C_137))
      | ~ r5_binop_1(k8_eqrel_1(A_134,B_135),k3_filter_1(A_134,B_135,C_136),k3_filter_1(A_134,B_135,C_137))
      | ~ r4_binop_1(k8_eqrel_1(A_134,B_135),k3_filter_1(A_134,B_135,C_136),k3_filter_1(A_134,B_135,C_137))
      | ~ v1_funct_1(k3_filter_1(A_134,B_135,C_137))
      | ~ v1_funct_1(k3_filter_1(A_134,B_135,C_136))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_134,A_134),A_134)))
      | ~ v1_funct_2(C_137,k2_zfmisc_1(A_134,A_134),A_134)
      | ~ v1_funct_1(C_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_134,A_134),A_134)))
      | ~ v1_funct_2(C_136,k2_zfmisc_1(A_134,A_134),A_134)
      | ~ v1_funct_1(C_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_134,A_134)))
      | ~ v8_relat_2(B_135)
      | ~ v3_relat_2(B_135)
      | ~ v1_partfun1(B_135,A_134)
      | v1_xboole_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_14,c_249])).

tff(c_28,plain,(
    ~ r6_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_260,plain,
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
    inference(resolution,[status(thm)],[c_253,c_28])).

tff(c_265,plain,
    ( ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_63,c_76,c_89,c_67,c_80,c_93,c_133,c_125,c_260])).

tff(c_266,plain,
    ( ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_265])).

tff(c_267,plain,(
    ~ r4_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_270,plain,
    ( ~ r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m2_filter_1('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_267])).

tff(c_273,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_146,c_270])).

tff(c_275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_273])).

tff(c_276,plain,(
    ~ r5_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k3_filter_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_280,plain,
    ( ~ r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m2_filter_1('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_276])).

tff(c_283,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_140,c_280])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:08:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.48  %$ v1_funct_2 > r6_binop_1 > r5_binop_1 > r4_binop_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.48  
% 3.08/1.48  %Foreground sorts:
% 3.08/1.48  
% 3.08/1.48  
% 3.08/1.48  %Background operators:
% 3.08/1.48  
% 3.08/1.48  
% 3.08/1.48  %Foreground operators:
% 3.08/1.48  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 3.08/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.48  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.08/1.48  tff(r6_binop_1, type, r6_binop_1: ($i * $i * $i) > $o).
% 3.08/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.48  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.08/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.48  tff(r4_binop_1, type, r4_binop_1: ($i * $i * $i) > $o).
% 3.08/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.48  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.48  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 3.08/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.48  tff(r5_binop_1, type, r5_binop_1: ($i * $i * $i) > $o).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.48  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 3.08/1.48  
% 3.08/1.51  tff(f_157, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m2_filter_1(C, A, B) => (![D]: (m2_filter_1(D, A, B) => (r6_binop_1(A, C, D) => r6_binop_1(k8_eqrel_1(A, B), k3_filter_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_filter_1)).
% 3.08/1.51  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.51  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.51  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.08/1.51  tff(f_53, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, k2_zfmisc_1(A, A), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r6_binop_1(A, B, C) <=> (r4_binop_1(A, B, C) & r5_binop_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_binop_1)).
% 3.08/1.51  tff(f_112, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m2_filter_1(C, A, B) => (![D]: (m2_filter_1(D, A, B) => (r5_binop_1(A, C, D) => r5_binop_1(k8_eqrel_1(A, B), k3_filter_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_filter_1)).
% 3.08/1.51  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m2_filter_1(C, A, B) => (![D]: (m2_filter_1(D, A, B) => (r4_binop_1(A, C, D) => r4_binop_1(k8_eqrel_1(A, B), k3_filter_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_filter_1)).
% 3.08/1.51  tff(f_76, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.08/1.51  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_42, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_40, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_38, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_34, plain, (m2_filter_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_32, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.51  tff(c_46, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.51  tff(c_49, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_46])).
% 3.08/1.51  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_49])).
% 3.08/1.51  tff(c_53, plain, (![C_62, A_63, B_64]: (v1_funct_1(C_62) | ~m2_filter_1(C_62, A_63, B_64) | ~v1_relat_1(B_64) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.51  tff(c_56, plain, (v1_funct_1('#skF_3') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_53])).
% 3.08/1.51  tff(c_62, plain, (v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56])).
% 3.08/1.51  tff(c_63, plain, (v1_funct_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_62])).
% 3.08/1.51  tff(c_68, plain, (![C_65, A_66, B_67]: (v1_funct_2(C_65, k2_zfmisc_1(A_66, A_66), A_66) | ~m2_filter_1(C_65, A_66, B_67) | ~v1_relat_1(B_67) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.51  tff(c_70, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_68])).
% 3.08/1.51  tff(c_75, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_70])).
% 3.08/1.51  tff(c_76, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_75])).
% 3.08/1.51  tff(c_81, plain, (![C_68, A_69, B_70]: (m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_69, A_69), A_69))) | ~m2_filter_1(C_68, A_69, B_70) | ~v1_relat_1(B_70) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.51  tff(c_83, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_81])).
% 3.08/1.51  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.08/1.51  tff(c_89, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_88])).
% 3.08/1.51  tff(c_59, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_53])).
% 3.08/1.51  tff(c_66, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_59])).
% 3.08/1.51  tff(c_67, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_66])).
% 3.08/1.51  tff(c_72, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_68])).
% 3.08/1.51  tff(c_79, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_72])).
% 3.08/1.51  tff(c_80, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_79])).
% 3.08/1.51  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_81])).
% 3.08/1.51  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_85])).
% 3.08/1.51  tff(c_93, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_92])).
% 3.08/1.51  tff(c_30, plain, (r6_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_135, plain, (![A_84, B_85, C_86]: (r5_binop_1(A_84, B_85, C_86) | ~r6_binop_1(A_84, B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84, A_84), A_84))) | ~v1_funct_2(C_86, k2_zfmisc_1(A_84, A_84), A_84) | ~v1_funct_1(C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_84, A_84), A_84))) | ~v1_funct_2(B_85, k2_zfmisc_1(A_84, A_84), A_84) | ~v1_funct_1(B_85))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.51  tff(c_137, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_135])).
% 3.08/1.51  tff(c_140, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_76, c_89, c_67, c_80, c_93, c_137])).
% 3.08/1.51  tff(c_24, plain, (![A_17, B_25, C_29, D_31]: (r5_binop_1(k8_eqrel_1(A_17, B_25), k3_filter_1(A_17, B_25, C_29), k3_filter_1(A_17, B_25, D_31)) | ~r5_binop_1(A_17, C_29, D_31) | ~m2_filter_1(D_31, A_17, B_25) | ~m2_filter_1(C_29, A_17, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v8_relat_2(B_25) | ~v3_relat_2(B_25) | ~v1_partfun1(B_25, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.08/1.51  tff(c_141, plain, (![A_87, B_88, C_89]: (r4_binop_1(A_87, B_88, C_89) | ~r6_binop_1(A_87, B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_87, A_87), A_87))) | ~v1_funct_2(C_89, k2_zfmisc_1(A_87, A_87), A_87) | ~v1_funct_1(C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_87, A_87), A_87))) | ~v1_funct_2(B_88, k2_zfmisc_1(A_87, A_87), A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.51  tff(c_143, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_141])).
% 3.08/1.51  tff(c_146, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_76, c_89, c_67, c_80, c_93, c_143])).
% 3.08/1.51  tff(c_26, plain, (![A_32, B_40, C_44, D_46]: (r4_binop_1(k8_eqrel_1(A_32, B_40), k3_filter_1(A_32, B_40, C_44), k3_filter_1(A_32, B_40, D_46)) | ~r4_binop_1(A_32, C_44, D_46) | ~m2_filter_1(D_46, A_32, B_40) | ~m2_filter_1(C_44, A_32, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v8_relat_2(B_40) | ~v3_relat_2(B_40) | ~v1_partfun1(B_40, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.51  tff(c_106, plain, (![A_71, B_72, C_73]: (v1_funct_1(k3_filter_1(A_71, B_72, C_73)) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_71, A_71), A_71))) | ~v1_funct_2(C_73, k2_zfmisc_1(A_71, A_71), A_71) | ~v1_funct_1(C_73) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1(A_71, A_71))) | ~v8_relat_2(B_72) | ~v3_relat_2(B_72) | ~v1_partfun1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.51  tff(c_110, plain, (![B_72]: (v1_funct_1(k3_filter_1('#skF_1', B_72, '#skF_3')) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_72) | ~v3_relat_2(B_72) | ~v1_partfun1(B_72, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_89, c_106])).
% 3.08/1.51  tff(c_117, plain, (![B_72]: (v1_funct_1(k3_filter_1('#skF_1', B_72, '#skF_3')) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_72) | ~v3_relat_2(B_72) | ~v1_partfun1(B_72, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_76, c_110])).
% 3.08/1.51  tff(c_127, plain, (![B_79]: (v1_funct_1(k3_filter_1('#skF_1', B_79, '#skF_3')) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_79) | ~v3_relat_2(B_79) | ~v1_partfun1(B_79, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_117])).
% 3.08/1.51  tff(c_130, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_3')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_127])).
% 3.08/1.51  tff(c_133, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_130])).
% 3.08/1.51  tff(c_108, plain, (![B_72]: (v1_funct_1(k3_filter_1('#skF_1', B_72, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_72) | ~v3_relat_2(B_72) | ~v1_partfun1(B_72, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_93, c_106])).
% 3.08/1.51  tff(c_113, plain, (![B_72]: (v1_funct_1(k3_filter_1('#skF_1', B_72, '#skF_4')) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_72) | ~v3_relat_2(B_72) | ~v1_partfun1(B_72, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_80, c_108])).
% 3.08/1.51  tff(c_119, plain, (![B_74]: (v1_funct_1(k3_filter_1('#skF_1', B_74, '#skF_4')) | ~m1_subset_1(B_74, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_74) | ~v3_relat_2(B_74) | ~v1_partfun1(B_74, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_113])).
% 3.08/1.51  tff(c_122, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_119])).
% 3.08/1.51  tff(c_125, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_122])).
% 3.08/1.51  tff(c_14, plain, (![A_10, B_11, C_12]: (v1_funct_2(k3_filter_1(A_10, B_11, C_12), k2_zfmisc_1(k8_eqrel_1(A_10, B_11), k8_eqrel_1(A_10, B_11)), k8_eqrel_1(A_10, B_11)) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_10, A_10), A_10))) | ~v1_funct_2(C_12, k2_zfmisc_1(A_10, A_10), A_10) | ~v1_funct_1(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))) | ~v8_relat_2(B_11) | ~v3_relat_2(B_11) | ~v1_partfun1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.51  tff(c_12, plain, (![A_10, B_11, C_12]: (m1_subset_1(k3_filter_1(A_10, B_11, C_12), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_10, B_11), k8_eqrel_1(A_10, B_11)), k8_eqrel_1(A_10, B_11)))) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_10, A_10), A_10))) | ~v1_funct_2(C_12, k2_zfmisc_1(A_10, A_10), A_10) | ~v1_funct_1(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))) | ~v8_relat_2(B_11) | ~v3_relat_2(B_11) | ~v1_partfun1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.51  tff(c_188, plain, (![A_98, B_99, C_100]: (m1_subset_1(k3_filter_1(A_98, B_99, C_100), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_98, B_99), k8_eqrel_1(A_98, B_99)), k8_eqrel_1(A_98, B_99)))) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_98, A_98), A_98))) | ~v1_funct_2(C_100, k2_zfmisc_1(A_98, A_98), A_98) | ~v1_funct_1(C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v8_relat_2(B_99) | ~v3_relat_2(B_99) | ~v1_partfun1(B_99, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.51  tff(c_6, plain, (![A_6, B_7, C_9]: (r6_binop_1(A_6, B_7, C_9) | ~r5_binop_1(A_6, B_7, C_9) | ~r4_binop_1(A_6, B_7, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_6, A_6), A_6))) | ~v1_funct_2(C_9, k2_zfmisc_1(A_6, A_6), A_6) | ~v1_funct_1(C_9) | ~m1_subset_1(B_7, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_6, A_6), A_6))) | ~v1_funct_2(B_7, k2_zfmisc_1(A_6, A_6), A_6) | ~v1_funct_1(B_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.51  tff(c_241, plain, (![A_122, B_123, B_124, C_125]: (r6_binop_1(k8_eqrel_1(A_122, B_123), B_124, k3_filter_1(A_122, B_123, C_125)) | ~r5_binop_1(k8_eqrel_1(A_122, B_123), B_124, k3_filter_1(A_122, B_123, C_125)) | ~r4_binop_1(k8_eqrel_1(A_122, B_123), B_124, k3_filter_1(A_122, B_123, C_125)) | ~v1_funct_2(k3_filter_1(A_122, B_123, C_125), k2_zfmisc_1(k8_eqrel_1(A_122, B_123), k8_eqrel_1(A_122, B_123)), k8_eqrel_1(A_122, B_123)) | ~v1_funct_1(k3_filter_1(A_122, B_123, C_125)) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_122, B_123), k8_eqrel_1(A_122, B_123)), k8_eqrel_1(A_122, B_123)))) | ~v1_funct_2(B_124, k2_zfmisc_1(k8_eqrel_1(A_122, B_123), k8_eqrel_1(A_122, B_123)), k8_eqrel_1(A_122, B_123)) | ~v1_funct_1(B_124) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_122, A_122), A_122))) | ~v1_funct_2(C_125, k2_zfmisc_1(A_122, A_122), A_122) | ~v1_funct_1(C_125) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_zfmisc_1(A_122, A_122))) | ~v8_relat_2(B_123) | ~v3_relat_2(B_123) | ~v1_partfun1(B_123, A_122) | v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_188, c_6])).
% 3.08/1.51  tff(c_245, plain, (![A_126, B_127, B_128, C_129]: (r6_binop_1(k8_eqrel_1(A_126, B_127), B_128, k3_filter_1(A_126, B_127, C_129)) | ~r5_binop_1(k8_eqrel_1(A_126, B_127), B_128, k3_filter_1(A_126, B_127, C_129)) | ~r4_binop_1(k8_eqrel_1(A_126, B_127), B_128, k3_filter_1(A_126, B_127, C_129)) | ~v1_funct_1(k3_filter_1(A_126, B_127, C_129)) | ~m1_subset_1(B_128, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_126, B_127), k8_eqrel_1(A_126, B_127)), k8_eqrel_1(A_126, B_127)))) | ~v1_funct_2(B_128, k2_zfmisc_1(k8_eqrel_1(A_126, B_127), k8_eqrel_1(A_126, B_127)), k8_eqrel_1(A_126, B_127)) | ~v1_funct_1(B_128) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_126, A_126), A_126))) | ~v1_funct_2(C_129, k2_zfmisc_1(A_126, A_126), A_126) | ~v1_funct_1(C_129) | ~m1_subset_1(B_127, k1_zfmisc_1(k2_zfmisc_1(A_126, A_126))) | ~v8_relat_2(B_127) | ~v3_relat_2(B_127) | ~v1_partfun1(B_127, A_126) | v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_14, c_241])).
% 3.08/1.51  tff(c_249, plain, (![A_130, B_131, C_132, C_133]: (r6_binop_1(k8_eqrel_1(A_130, B_131), k3_filter_1(A_130, B_131, C_132), k3_filter_1(A_130, B_131, C_133)) | ~r5_binop_1(k8_eqrel_1(A_130, B_131), k3_filter_1(A_130, B_131, C_132), k3_filter_1(A_130, B_131, C_133)) | ~r4_binop_1(k8_eqrel_1(A_130, B_131), k3_filter_1(A_130, B_131, C_132), k3_filter_1(A_130, B_131, C_133)) | ~v1_funct_1(k3_filter_1(A_130, B_131, C_133)) | ~v1_funct_2(k3_filter_1(A_130, B_131, C_132), k2_zfmisc_1(k8_eqrel_1(A_130, B_131), k8_eqrel_1(A_130, B_131)), k8_eqrel_1(A_130, B_131)) | ~v1_funct_1(k3_filter_1(A_130, B_131, C_132)) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_130, A_130), A_130))) | ~v1_funct_2(C_133, k2_zfmisc_1(A_130, A_130), A_130) | ~v1_funct_1(C_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_130, A_130), A_130))) | ~v1_funct_2(C_132, k2_zfmisc_1(A_130, A_130), A_130) | ~v1_funct_1(C_132) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_zfmisc_1(A_130, A_130))) | ~v8_relat_2(B_131) | ~v3_relat_2(B_131) | ~v1_partfun1(B_131, A_130) | v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_12, c_245])).
% 3.08/1.51  tff(c_253, plain, (![A_134, B_135, C_136, C_137]: (r6_binop_1(k8_eqrel_1(A_134, B_135), k3_filter_1(A_134, B_135, C_136), k3_filter_1(A_134, B_135, C_137)) | ~r5_binop_1(k8_eqrel_1(A_134, B_135), k3_filter_1(A_134, B_135, C_136), k3_filter_1(A_134, B_135, C_137)) | ~r4_binop_1(k8_eqrel_1(A_134, B_135), k3_filter_1(A_134, B_135, C_136), k3_filter_1(A_134, B_135, C_137)) | ~v1_funct_1(k3_filter_1(A_134, B_135, C_137)) | ~v1_funct_1(k3_filter_1(A_134, B_135, C_136)) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_134, A_134), A_134))) | ~v1_funct_2(C_137, k2_zfmisc_1(A_134, A_134), A_134) | ~v1_funct_1(C_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_134, A_134), A_134))) | ~v1_funct_2(C_136, k2_zfmisc_1(A_134, A_134), A_134) | ~v1_funct_1(C_136) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_134, A_134))) | ~v8_relat_2(B_135) | ~v3_relat_2(B_135) | ~v1_partfun1(B_135, A_134) | v1_xboole_0(A_134))), inference(resolution, [status(thm)], [c_14, c_249])).
% 3.08/1.51  tff(c_28, plain, (~r6_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.08/1.51  tff(c_260, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_253, c_28])).
% 3.08/1.51  tff(c_265, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_63, c_76, c_89, c_67, c_80, c_93, c_133, c_125, c_260])).
% 3.08/1.51  tff(c_266, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_265])).
% 3.08/1.51  tff(c_267, plain, (~r4_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_266])).
% 3.08/1.51  tff(c_270, plain, (~r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m2_filter_1('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_267])).
% 3.08/1.51  tff(c_273, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_146, c_270])).
% 3.08/1.51  tff(c_275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_273])).
% 3.08/1.51  tff(c_276, plain, (~r5_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k3_filter_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_266])).
% 3.08/1.51  tff(c_280, plain, (~r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m2_filter_1('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_276])).
% 3.08/1.51  tff(c_283, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_140, c_280])).
% 3.08/1.51  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_283])).
% 3.08/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.51  
% 3.08/1.51  Inference rules
% 3.08/1.51  ----------------------
% 3.08/1.51  #Ref     : 0
% 3.08/1.51  #Sup     : 39
% 3.08/1.51  #Fact    : 0
% 3.08/1.51  #Define  : 0
% 3.08/1.51  #Split   : 4
% 3.08/1.51  #Chain   : 0
% 3.08/1.51  #Close   : 0
% 3.08/1.51  
% 3.08/1.51  Ordering : KBO
% 3.08/1.51  
% 3.08/1.51  Simplification rules
% 3.08/1.51  ----------------------
% 3.08/1.51  #Subsume      : 4
% 3.08/1.51  #Demod        : 83
% 3.08/1.51  #Tautology    : 3
% 3.08/1.51  #SimpNegUnit  : 13
% 3.08/1.51  #BackRed      : 0
% 3.08/1.51  
% 3.08/1.51  #Partial instantiations: 0
% 3.08/1.51  #Strategies tried      : 1
% 3.08/1.51  
% 3.08/1.51  Timing (in seconds)
% 3.08/1.51  ----------------------
% 3.08/1.51  Preprocessing        : 0.34
% 3.08/1.51  Parsing              : 0.20
% 3.08/1.51  CNF conversion       : 0.03
% 3.08/1.51  Main loop            : 0.33
% 3.08/1.51  Inferencing          : 0.14
% 3.08/1.51  Reduction            : 0.09
% 3.08/1.51  Demodulation         : 0.07
% 3.08/1.51  BG Simplification    : 0.02
% 3.08/1.51  Subsumption          : 0.06
% 3.08/1.51  Abstraction          : 0.01
% 3.08/1.51  MUC search           : 0.00
% 3.08/1.51  Cooper               : 0.00
% 3.08/1.51  Total                : 0.72
% 3.08/1.51  Index Insertion      : 0.00
% 3.08/1.51  Index Deletion       : 0.00
% 3.08/1.51  Index Matching       : 0.00
% 3.08/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
