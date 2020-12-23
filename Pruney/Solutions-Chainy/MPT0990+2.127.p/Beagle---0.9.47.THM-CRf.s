%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:14 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  198 (2795 expanded)
%              Number of leaves         :   48 ( 992 expanded)
%              Depth                    :   24
%              Number of atoms          :  452 (8941 expanded)
%              Number of equality atoms :  132 (2644 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_222,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_113,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_196,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_180,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_68,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_158,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_158])).

tff(c_176,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_167])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_212,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_224,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_212])).

tff(c_52,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_16,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_96,plain,(
    ! [A_18] : k2_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_3096,plain,(
    ! [A_195,B_200,F_196,E_198,D_199,C_197] :
      ( m1_subset_1(k1_partfun1(A_195,B_200,C_197,D_199,E_198,F_196),k1_zfmisc_1(k2_zfmisc_1(A_195,D_199)))
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_197,D_199)))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_195,B_200)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_91,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1285,plain,(
    ! [D_134,C_135,A_136,B_137] :
      ( D_134 = C_135
      | ~ r2_relset_1(A_136,B_137,C_135,D_134)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1293,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_1285])).

tff(c_1308,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1293])).

tff(c_1545,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_3116,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3096,c_1545])).

tff(c_3141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_3116])).

tff(c_3142,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_4203,plain,(
    ! [B_250,A_246,E_245,D_248,F_249,C_247] :
      ( k1_partfun1(A_246,B_250,C_247,D_248,E_245,F_249) = k5_relat_1(E_245,F_249)
      | ~ m1_subset_1(F_249,k1_zfmisc_1(k2_zfmisc_1(C_247,D_248)))
      | ~ v1_funct_1(F_249)
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_246,B_250)))
      | ~ v1_funct_1(E_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4209,plain,(
    ! [A_246,B_250,E_245] :
      ( k1_partfun1(A_246,B_250,'#skF_2','#skF_1',E_245,'#skF_4') = k5_relat_1(E_245,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_246,B_250)))
      | ~ v1_funct_1(E_245) ) ),
    inference(resolution,[status(thm)],[c_80,c_4203])).

tff(c_4234,plain,(
    ! [A_254,B_255,E_256] :
      ( k1_partfun1(A_254,B_255,'#skF_2','#skF_1',E_256,'#skF_4') = k5_relat_1(E_256,'#skF_4')
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255)))
      | ~ v1_funct_1(E_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4209])).

tff(c_4240,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_4234])).

tff(c_4247,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3142,c_4240])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_158])).

tff(c_173,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_164])).

tff(c_78,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_308,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_314,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_308])).

tff(c_321,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_314])).

tff(c_373,plain,(
    ! [B_107,A_108] :
      ( k2_relat_1(k5_relat_1(B_107,A_108)) = k2_relat_1(A_108)
      | ~ r1_tarski(k1_relat_1(A_108),k2_relat_1(B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_376,plain,(
    ! [A_108] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_108)) = k2_relat_1(A_108)
      | ~ r1_tarski(k1_relat_1(A_108),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_373])).

tff(c_440,plain,(
    ! [A_111] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_111)) = k2_relat_1(A_111)
      | ~ r1_tarski(k1_relat_1(A_111),'#skF_2')
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_376])).

tff(c_451,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_5)) = k2_relat_1(B_5)
      | ~ v4_relat_1(B_5,'#skF_2')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_440])).

tff(c_4266,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4247,c_451])).

tff(c_4278,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_224,c_96,c_4266])).

tff(c_322,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_308])).

tff(c_4280,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4278,c_322])).

tff(c_4354,plain,(
    ! [B_257,C_258,A_259] :
      ( k6_partfun1(B_257) = k5_relat_1(k2_funct_1(C_258),C_258)
      | k1_xboole_0 = B_257
      | ~ v2_funct_1(C_258)
      | k2_relset_1(A_259,B_257,C_258) != B_257
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_259,B_257)))
      | ~ v1_funct_2(C_258,A_259,B_257)
      | ~ v1_funct_1(C_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_4360,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_4354])).

tff(c_4370,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4280,c_4360])).

tff(c_4371,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4370])).

tff(c_4498,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4371])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_28,plain,(
    ! [A_22] : v2_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,(
    ! [A_22] : v2_funct_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_5052,plain,(
    ! [D_285,B_286,E_282,A_284,C_283] :
      ( k1_xboole_0 = C_283
      | v2_funct_1(E_282)
      | k2_relset_1(A_284,B_286,D_285) != B_286
      | ~ v2_funct_1(k1_partfun1(A_284,B_286,B_286,C_283,D_285,E_282))
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(B_286,C_283)))
      | ~ v1_funct_2(E_282,B_286,C_283)
      | ~ v1_funct_1(E_282)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1(A_284,B_286)))
      | ~ v1_funct_2(D_285,A_284,B_286)
      | ~ v1_funct_1(D_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_5056,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3142,c_5052])).

tff(c_5061,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_92,c_78,c_5056])).

tff(c_5063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4498,c_72,c_5061])).

tff(c_5065,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4371])).

tff(c_24,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_287,plain,(
    ! [A_101] :
      ( k1_relat_1(k2_funct_1(A_101)) = k2_relat_1(A_101)
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_222,plain,(
    ! [A_34] : v4_relat_1(k6_partfun1(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_91,c_212])).

tff(c_26,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_93,plain,(
    ! [A_22] : v1_relat_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26])).

tff(c_14,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    ! [A_18] : k1_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_225,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k1_relat_1(B_89),A_90)
      | ~ v4_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_231,plain,(
    ! [A_18,A_90] :
      ( r1_tarski(A_18,A_90)
      | ~ v4_relat_1(k6_partfun1(A_18),A_90)
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_225])).

tff(c_236,plain,(
    ! [A_92,A_93] :
      ( r1_tarski(A_92,A_93)
      | ~ v4_relat_1(k6_partfun1(A_92),A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_231])).

tff(c_255,plain,(
    ! [A_97] : r1_tarski(A_97,A_97) ),
    inference(resolution,[status(thm)],[c_222,c_236])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_260,plain,(
    ! [B_5] :
      ( v4_relat_1(B_5,k1_relat_1(B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_255,c_4])).

tff(c_293,plain,(
    ! [A_101] :
      ( v4_relat_1(k2_funct_1(A_101),k2_relat_1(A_101))
      | ~ v1_relat_1(k2_funct_1(A_101))
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_260])).

tff(c_4305,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4278,c_293])).

tff(c_4326,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_84,c_4305])).

tff(c_5127,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5065,c_4326])).

tff(c_5128,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5127])).

tff(c_5131,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_5128])).

tff(c_5135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_84,c_5131])).

tff(c_5137,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5127])).

tff(c_5136,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5127])).

tff(c_5138,plain,(
    ! [A_287,C_288,B_289] :
      ( k6_partfun1(A_287) = k5_relat_1(C_288,k2_funct_1(C_288))
      | k1_xboole_0 = B_289
      | ~ v2_funct_1(C_288)
      | k2_relset_1(A_287,B_289,C_288) != B_289
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_287,B_289)))
      | ~ v1_funct_2(C_288,A_287,B_289)
      | ~ v1_funct_1(C_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_5144,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_5138])).

tff(c_5154,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4280,c_5065,c_5144])).

tff(c_5155,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5154])).

tff(c_395,plain,(
    ! [B_107,B_5] :
      ( k2_relat_1(k5_relat_1(B_107,B_5)) = k2_relat_1(B_5)
      | ~ v1_relat_1(B_107)
      | ~ v4_relat_1(B_5,k2_relat_1(B_107))
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_4299,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_5)) = k2_relat_1(B_5)
      | ~ v1_relat_1('#skF_4')
      | ~ v4_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4278,c_395])).

tff(c_6207,plain,(
    ! [B_328] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_328)) = k2_relat_1(B_328)
      | ~ v4_relat_1(B_328,'#skF_1')
      | ~ v1_relat_1(B_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_4299])).

tff(c_6257,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5155,c_6207])).

tff(c_6288,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5137,c_5136,c_96,c_6257])).

tff(c_30,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6326,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6288,c_30])).

tff(c_6352,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_84,c_5065,c_6326])).

tff(c_20,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_partfun1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_4308,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4278,c_94])).

tff(c_4328,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_4308])).

tff(c_18,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_19)),A_19) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_19)),A_19) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_644,plain,(
    ! [A_119,B_120,C_121] :
      ( k5_relat_1(k5_relat_1(A_119,B_120),C_121) = k5_relat_1(A_119,k5_relat_1(B_120,C_121))
      | ~ v1_relat_1(C_121)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_680,plain,(
    ! [A_19,C_121] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_19)),k5_relat_1(A_19,C_121)) = k5_relat_1(A_19,C_121)
      | ~ v1_relat_1(C_121)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_644])).

tff(c_696,plain,(
    ! [A_19,C_121] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_19)),k5_relat_1(A_19,C_121)) = k5_relat_1(A_19,C_121)
      | ~ v1_relat_1(C_121)
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_680])).

tff(c_4337,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4328,c_696])).

tff(c_4347,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_93,c_4328,c_4337])).

tff(c_6359,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6352,c_4347])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_349,plain,(
    ! [A_106] :
      ( v4_relat_1(k2_funct_1(A_106),k2_relat_1(A_106))
      | ~ v1_relat_1(k2_funct_1(A_106))
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_260])).

tff(c_352,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_349])).

tff(c_360,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_74,c_352])).

tff(c_363,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_366,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_366])).

tff(c_372,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_243,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_222,c_236])).

tff(c_1476,plain,(
    ! [A_140] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_140)),k2_funct_1(A_140)) = k2_funct_1(A_140)
      | ~ v1_relat_1(k2_funct_1(A_140))
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_95])).

tff(c_1524,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_1476])).

tff(c_1542,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_74,c_372,c_1524])).

tff(c_12,plain,(
    ! [A_11,B_15,C_17] :
      ( k5_relat_1(k5_relat_1(A_11,B_15),C_17) = k5_relat_1(A_11,k5_relat_1(B_15,C_17))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3159,plain,(
    ! [C_17] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_17)) = k5_relat_1(k2_funct_1('#skF_3'),C_17)
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1542,c_12])).

tff(c_3188,plain,(
    ! [C_201] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_201)) = k5_relat_1(k2_funct_1('#skF_3'),C_201)
      | ~ v1_relat_1(C_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_372,c_3159])).

tff(c_3220,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_3188])).

tff(c_3234,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_93,c_1542,c_3220])).

tff(c_3260,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3234])).

tff(c_3285,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_74,c_3260])).

tff(c_389,plain,(
    ! [B_107,A_18] :
      ( k2_relat_1(k5_relat_1(B_107,k6_partfun1(A_18))) = k2_relat_1(k6_partfun1(A_18))
      | ~ r1_tarski(A_18,k2_relat_1(B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_373])).

tff(c_397,plain,(
    ! [B_107,A_18] :
      ( k2_relat_1(k5_relat_1(B_107,k6_partfun1(A_18))) = A_18
      | ~ r1_tarski(A_18,k2_relat_1(B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_96,c_389])).

tff(c_3301,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3285,c_397])).

tff(c_3311,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_3301])).

tff(c_3372,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3311])).

tff(c_3389,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3372])).

tff(c_3395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_74,c_243,c_3389])).

tff(c_3396,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3311])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_5142,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_5138])).

tff(c_5150,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_5142])).

tff(c_5151,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5150])).

tff(c_32,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_443,plain,(
    ! [A_23] :
      ( k2_relat_1(k5_relat_1('#skF_3',k2_funct_1(A_23))) = k2_relat_1(k2_funct_1(A_23))
      | ~ r1_tarski(k2_relat_1(A_23),'#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_440])).

tff(c_5168,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5151,c_443])).

tff(c_5184,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_74,c_372,c_243,c_321,c_96,c_3396,c_5168])).

tff(c_5210,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5184,c_3285])).

tff(c_4358,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_4354])).

tff(c_4366,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_4358])).

tff(c_4367,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4366])).

tff(c_4393,plain,(
    ! [C_17] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_17)) = k5_relat_1(k6_partfun1('#skF_2'),C_17)
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_12])).

tff(c_6929,plain,(
    ! [C_338] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_338)) = k5_relat_1(k6_partfun1('#skF_2'),C_338)
      | ~ v1_relat_1(C_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_173,c_4393])).

tff(c_6953,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4247,c_6929])).

tff(c_6977,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_6359,c_5210,c_6953])).

tff(c_6979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.55/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.56  
% 7.55/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.56  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.55/2.56  
% 7.55/2.56  %Foreground sorts:
% 7.55/2.56  
% 7.55/2.56  
% 7.55/2.56  %Background operators:
% 7.55/2.56  
% 7.55/2.56  
% 7.55/2.56  %Foreground operators:
% 7.55/2.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.55/2.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.55/2.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.55/2.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.55/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.55/2.56  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.55/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.55/2.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.55/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.55/2.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.55/2.56  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.55/2.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.55/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.55/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.55/2.56  tff('#skF_1', type, '#skF_1': $i).
% 7.55/2.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.55/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.55/2.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.55/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.55/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.55/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.55/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.55/2.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.55/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.55/2.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.55/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.55/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.55/2.56  
% 7.97/2.59  tff(f_222, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.97/2.59  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.97/2.59  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.97/2.59  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.97/2.59  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.97/2.59  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.97/2.59  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.97/2.59  tff(f_113, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.97/2.59  tff(f_111, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.97/2.59  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.97/2.59  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.97/2.59  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.97/2.59  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 7.97/2.59  tff(f_196, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.97/2.59  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.97/2.59  tff(f_180, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.97/2.59  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.97/2.59  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.97/2.59  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.97/2.59  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.97/2.59  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.97/2.59  tff(c_68, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.97/2.59  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_158, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.97/2.59  tff(c_167, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_158])).
% 7.97/2.59  tff(c_176, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_167])).
% 7.97/2.59  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_72, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_212, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.97/2.59  tff(c_224, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_212])).
% 7.97/2.59  tff(c_52, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.97/2.59  tff(c_16, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.97/2.59  tff(c_96, plain, (![A_18]: (k2_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 7.97/2.59  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_3096, plain, (![A_195, B_200, F_196, E_198, D_199, C_197]: (m1_subset_1(k1_partfun1(A_195, B_200, C_197, D_199, E_198, F_196), k1_zfmisc_1(k2_zfmisc_1(A_195, D_199))) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_197, D_199))) | ~v1_funct_1(F_196) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_195, B_200))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.97/2.59  tff(c_44, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.97/2.59  tff(c_91, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44])).
% 7.97/2.59  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_1285, plain, (![D_134, C_135, A_136, B_137]: (D_134=C_135 | ~r2_relset_1(A_136, B_137, C_135, D_134) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.97/2.59  tff(c_1293, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_1285])).
% 7.97/2.59  tff(c_1308, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1293])).
% 7.97/2.59  tff(c_1545, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1308])).
% 7.97/2.59  tff(c_3116, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3096, c_1545])).
% 7.97/2.59  tff(c_3141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_3116])).
% 7.97/2.59  tff(c_3142, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1308])).
% 7.97/2.59  tff(c_4203, plain, (![B_250, A_246, E_245, D_248, F_249, C_247]: (k1_partfun1(A_246, B_250, C_247, D_248, E_245, F_249)=k5_relat_1(E_245, F_249) | ~m1_subset_1(F_249, k1_zfmisc_1(k2_zfmisc_1(C_247, D_248))) | ~v1_funct_1(F_249) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_246, B_250))) | ~v1_funct_1(E_245))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.97/2.59  tff(c_4209, plain, (![A_246, B_250, E_245]: (k1_partfun1(A_246, B_250, '#skF_2', '#skF_1', E_245, '#skF_4')=k5_relat_1(E_245, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_246, B_250))) | ~v1_funct_1(E_245))), inference(resolution, [status(thm)], [c_80, c_4203])).
% 7.97/2.59  tff(c_4234, plain, (![A_254, B_255, E_256]: (k1_partfun1(A_254, B_255, '#skF_2', '#skF_1', E_256, '#skF_4')=k5_relat_1(E_256, '#skF_4') | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))) | ~v1_funct_1(E_256))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4209])).
% 7.97/2.59  tff(c_4240, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_4234])).
% 7.97/2.59  tff(c_4247, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3142, c_4240])).
% 7.97/2.59  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/2.59  tff(c_164, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_158])).
% 7.97/2.59  tff(c_173, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_164])).
% 7.97/2.59  tff(c_78, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_308, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.97/2.59  tff(c_314, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_308])).
% 7.97/2.59  tff(c_321, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_314])).
% 7.97/2.59  tff(c_373, plain, (![B_107, A_108]: (k2_relat_1(k5_relat_1(B_107, A_108))=k2_relat_1(A_108) | ~r1_tarski(k1_relat_1(A_108), k2_relat_1(B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/2.59  tff(c_376, plain, (![A_108]: (k2_relat_1(k5_relat_1('#skF_3', A_108))=k2_relat_1(A_108) | ~r1_tarski(k1_relat_1(A_108), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_321, c_373])).
% 7.97/2.59  tff(c_440, plain, (![A_111]: (k2_relat_1(k5_relat_1('#skF_3', A_111))=k2_relat_1(A_111) | ~r1_tarski(k1_relat_1(A_111), '#skF_2') | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_376])).
% 7.97/2.59  tff(c_451, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_3', B_5))=k2_relat_1(B_5) | ~v4_relat_1(B_5, '#skF_2') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_440])).
% 7.97/2.59  tff(c_4266, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1('#skF_4') | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4247, c_451])).
% 7.97/2.59  tff(c_4278, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_224, c_96, c_4266])).
% 7.97/2.59  tff(c_322, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_308])).
% 7.97/2.59  tff(c_4280, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4278, c_322])).
% 7.97/2.59  tff(c_4354, plain, (![B_257, C_258, A_259]: (k6_partfun1(B_257)=k5_relat_1(k2_funct_1(C_258), C_258) | k1_xboole_0=B_257 | ~v2_funct_1(C_258) | k2_relset_1(A_259, B_257, C_258)!=B_257 | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_259, B_257))) | ~v1_funct_2(C_258, A_259, B_257) | ~v1_funct_1(C_258))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.97/2.59  tff(c_4360, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_4354])).
% 7.97/2.59  tff(c_4370, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_4280, c_4360])).
% 7.97/2.59  tff(c_4371, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_4370])).
% 7.97/2.59  tff(c_4498, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_4371])).
% 7.97/2.59  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_28, plain, (![A_22]: (v2_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.97/2.59  tff(c_92, plain, (![A_22]: (v2_funct_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 7.97/2.59  tff(c_5052, plain, (![D_285, B_286, E_282, A_284, C_283]: (k1_xboole_0=C_283 | v2_funct_1(E_282) | k2_relset_1(A_284, B_286, D_285)!=B_286 | ~v2_funct_1(k1_partfun1(A_284, B_286, B_286, C_283, D_285, E_282)) | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(B_286, C_283))) | ~v1_funct_2(E_282, B_286, C_283) | ~v1_funct_1(E_282) | ~m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1(A_284, B_286))) | ~v1_funct_2(D_285, A_284, B_286) | ~v1_funct_1(D_285))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.97/2.59  tff(c_5056, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3142, c_5052])).
% 7.97/2.59  tff(c_5061, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_92, c_78, c_5056])).
% 7.97/2.59  tff(c_5063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4498, c_72, c_5061])).
% 7.97/2.59  tff(c_5065, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_4371])).
% 7.97/2.59  tff(c_24, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.97/2.59  tff(c_287, plain, (![A_101]: (k1_relat_1(k2_funct_1(A_101))=k2_relat_1(A_101) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.97/2.59  tff(c_222, plain, (![A_34]: (v4_relat_1(k6_partfun1(A_34), A_34))), inference(resolution, [status(thm)], [c_91, c_212])).
% 7.97/2.59  tff(c_26, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.97/2.59  tff(c_93, plain, (![A_22]: (v1_relat_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_26])).
% 7.97/2.59  tff(c_14, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.97/2.59  tff(c_97, plain, (![A_18]: (k1_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14])).
% 7.97/2.59  tff(c_225, plain, (![B_89, A_90]: (r1_tarski(k1_relat_1(B_89), A_90) | ~v4_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/2.59  tff(c_231, plain, (![A_18, A_90]: (r1_tarski(A_18, A_90) | ~v4_relat_1(k6_partfun1(A_18), A_90) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_225])).
% 7.97/2.59  tff(c_236, plain, (![A_92, A_93]: (r1_tarski(A_92, A_93) | ~v4_relat_1(k6_partfun1(A_92), A_93))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_231])).
% 7.97/2.59  tff(c_255, plain, (![A_97]: (r1_tarski(A_97, A_97))), inference(resolution, [status(thm)], [c_222, c_236])).
% 7.97/2.59  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/2.59  tff(c_260, plain, (![B_5]: (v4_relat_1(B_5, k1_relat_1(B_5)) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_255, c_4])).
% 7.97/2.59  tff(c_293, plain, (![A_101]: (v4_relat_1(k2_funct_1(A_101), k2_relat_1(A_101)) | ~v1_relat_1(k2_funct_1(A_101)) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_287, c_260])).
% 7.97/2.59  tff(c_4305, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4278, c_293])).
% 7.97/2.59  tff(c_4326, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_84, c_4305])).
% 7.97/2.59  tff(c_5127, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5065, c_4326])).
% 7.97/2.59  tff(c_5128, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5127])).
% 7.97/2.59  tff(c_5131, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_5128])).
% 7.97/2.59  tff(c_5135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_84, c_5131])).
% 7.97/2.59  tff(c_5137, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5127])).
% 7.97/2.59  tff(c_5136, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_5127])).
% 7.97/2.59  tff(c_5138, plain, (![A_287, C_288, B_289]: (k6_partfun1(A_287)=k5_relat_1(C_288, k2_funct_1(C_288)) | k1_xboole_0=B_289 | ~v2_funct_1(C_288) | k2_relset_1(A_287, B_289, C_288)!=B_289 | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_287, B_289))) | ~v1_funct_2(C_288, A_287, B_289) | ~v1_funct_1(C_288))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.97/2.59  tff(c_5144, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_5138])).
% 7.97/2.59  tff(c_5154, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_4280, c_5065, c_5144])).
% 7.97/2.59  tff(c_5155, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_5154])).
% 7.97/2.59  tff(c_395, plain, (![B_107, B_5]: (k2_relat_1(k5_relat_1(B_107, B_5))=k2_relat_1(B_5) | ~v1_relat_1(B_107) | ~v4_relat_1(B_5, k2_relat_1(B_107)) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_373])).
% 7.97/2.59  tff(c_4299, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_4', B_5))=k2_relat_1(B_5) | ~v1_relat_1('#skF_4') | ~v4_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_4278, c_395])).
% 7.97/2.59  tff(c_6207, plain, (![B_328]: (k2_relat_1(k5_relat_1('#skF_4', B_328))=k2_relat_1(B_328) | ~v4_relat_1(B_328, '#skF_1') | ~v1_relat_1(B_328))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_4299])).
% 7.97/2.59  tff(c_6257, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5155, c_6207])).
% 7.97/2.59  tff(c_6288, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5137, c_5136, c_96, c_6257])).
% 7.97/2.59  tff(c_30, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.97/2.59  tff(c_6326, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6288, c_30])).
% 7.97/2.59  tff(c_6352, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_84, c_5065, c_6326])).
% 7.97/2.59  tff(c_20, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/2.59  tff(c_94, plain, (![A_20]: (k5_relat_1(A_20, k6_partfun1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 7.97/2.59  tff(c_4308, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4278, c_94])).
% 7.97/2.59  tff(c_4328, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_4308])).
% 7.97/2.59  tff(c_18, plain, (![A_19]: (k5_relat_1(k6_relat_1(k1_relat_1(A_19)), A_19)=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.97/2.59  tff(c_95, plain, (![A_19]: (k5_relat_1(k6_partfun1(k1_relat_1(A_19)), A_19)=A_19 | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 7.97/2.59  tff(c_644, plain, (![A_119, B_120, C_121]: (k5_relat_1(k5_relat_1(A_119, B_120), C_121)=k5_relat_1(A_119, k5_relat_1(B_120, C_121)) | ~v1_relat_1(C_121) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.97/2.59  tff(c_680, plain, (![A_19, C_121]: (k5_relat_1(k6_partfun1(k1_relat_1(A_19)), k5_relat_1(A_19, C_121))=k5_relat_1(A_19, C_121) | ~v1_relat_1(C_121) | ~v1_relat_1(A_19) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_95, c_644])).
% 7.97/2.59  tff(c_696, plain, (![A_19, C_121]: (k5_relat_1(k6_partfun1(k1_relat_1(A_19)), k5_relat_1(A_19, C_121))=k5_relat_1(A_19, C_121) | ~v1_relat_1(C_121) | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_680])).
% 7.97/2.59  tff(c_4337, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4328, c_696])).
% 7.97/2.59  tff(c_4347, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_93, c_4328, c_4337])).
% 7.97/2.59  tff(c_6359, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6352, c_4347])).
% 7.97/2.59  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_349, plain, (![A_106]: (v4_relat_1(k2_funct_1(A_106), k2_relat_1(A_106)) | ~v1_relat_1(k2_funct_1(A_106)) | ~v2_funct_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_287, c_260])).
% 7.97/2.59  tff(c_352, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_321, c_349])).
% 7.97/2.59  tff(c_360, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_74, c_352])).
% 7.97/2.59  tff(c_363, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_360])).
% 7.97/2.59  tff(c_366, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_363])).
% 7.97/2.59  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_366])).
% 7.97/2.59  tff(c_372, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_360])).
% 7.97/2.59  tff(c_243, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_222, c_236])).
% 7.97/2.59  tff(c_1476, plain, (![A_140]: (k5_relat_1(k6_partfun1(k2_relat_1(A_140)), k2_funct_1(A_140))=k2_funct_1(A_140) | ~v1_relat_1(k2_funct_1(A_140)) | ~v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_287, c_95])).
% 7.97/2.59  tff(c_1524, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_321, c_1476])).
% 7.97/2.59  tff(c_1542, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_74, c_372, c_1524])).
% 7.97/2.59  tff(c_12, plain, (![A_11, B_15, C_17]: (k5_relat_1(k5_relat_1(A_11, B_15), C_17)=k5_relat_1(A_11, k5_relat_1(B_15, C_17)) | ~v1_relat_1(C_17) | ~v1_relat_1(B_15) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.97/2.59  tff(c_3159, plain, (![C_17]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_17))=k5_relat_1(k2_funct_1('#skF_3'), C_17) | ~v1_relat_1(C_17) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1542, c_12])).
% 7.97/2.59  tff(c_3188, plain, (![C_201]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_201))=k5_relat_1(k2_funct_1('#skF_3'), C_201) | ~v1_relat_1(C_201))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_372, c_3159])).
% 7.97/2.59  tff(c_3220, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_3188])).
% 7.97/2.59  tff(c_3234, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_93, c_1542, c_3220])).
% 7.97/2.59  tff(c_3260, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3234])).
% 7.97/2.59  tff(c_3285, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_74, c_3260])).
% 7.97/2.59  tff(c_389, plain, (![B_107, A_18]: (k2_relat_1(k5_relat_1(B_107, k6_partfun1(A_18)))=k2_relat_1(k6_partfun1(A_18)) | ~r1_tarski(A_18, k2_relat_1(B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_373])).
% 7.97/2.59  tff(c_397, plain, (![B_107, A_18]: (k2_relat_1(k5_relat_1(B_107, k6_partfun1(A_18)))=A_18 | ~r1_tarski(A_18, k2_relat_1(B_107)) | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_96, c_389])).
% 7.97/2.59  tff(c_3301, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3285, c_397])).
% 7.97/2.59  tff(c_3311, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_3301])).
% 7.97/2.59  tff(c_3372, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3311])).
% 7.97/2.59  tff(c_3389, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3372])).
% 7.97/2.59  tff(c_3395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_74, c_243, c_3389])).
% 7.97/2.59  tff(c_3396, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3311])).
% 7.97/2.59  tff(c_70, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.97/2.59  tff(c_5142, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_5138])).
% 7.97/2.59  tff(c_5150, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_5142])).
% 7.97/2.59  tff(c_5151, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_5150])).
% 7.97/2.59  tff(c_32, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.97/2.59  tff(c_443, plain, (![A_23]: (k2_relat_1(k5_relat_1('#skF_3', k2_funct_1(A_23)))=k2_relat_1(k2_funct_1(A_23)) | ~r1_tarski(k2_relat_1(A_23), '#skF_2') | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_32, c_440])).
% 7.97/2.59  tff(c_5168, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5151, c_443])).
% 7.97/2.59  tff(c_5184, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_74, c_372, c_243, c_321, c_96, c_3396, c_5168])).
% 7.97/2.59  tff(c_5210, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5184, c_3285])).
% 7.97/2.59  tff(c_4358, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_4354])).
% 7.97/2.59  tff(c_4366, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_4358])).
% 7.97/2.59  tff(c_4367, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_4366])).
% 7.97/2.59  tff(c_4393, plain, (![C_17]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_17))=k5_relat_1(k6_partfun1('#skF_2'), C_17) | ~v1_relat_1(C_17) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_12])).
% 7.97/2.59  tff(c_6929, plain, (![C_338]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_338))=k5_relat_1(k6_partfun1('#skF_2'), C_338) | ~v1_relat_1(C_338))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_173, c_4393])).
% 7.97/2.59  tff(c_6953, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4247, c_6929])).
% 7.97/2.59  tff(c_6977, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_6359, c_5210, c_6953])).
% 7.97/2.59  tff(c_6979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_6977])).
% 7.97/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.59  
% 7.97/2.59  Inference rules
% 7.97/2.59  ----------------------
% 7.97/2.59  #Ref     : 0
% 7.97/2.59  #Sup     : 1483
% 7.97/2.59  #Fact    : 0
% 7.97/2.59  #Define  : 0
% 7.97/2.59  #Split   : 19
% 7.97/2.59  #Chain   : 0
% 7.97/2.59  #Close   : 0
% 7.97/2.59  
% 7.97/2.59  Ordering : KBO
% 7.97/2.59  
% 7.97/2.59  Simplification rules
% 7.97/2.59  ----------------------
% 7.97/2.59  #Subsume      : 39
% 7.97/2.59  #Demod        : 2481
% 7.97/2.59  #Tautology    : 792
% 7.97/2.59  #SimpNegUnit  : 37
% 7.97/2.59  #BackRed      : 82
% 7.97/2.59  
% 7.97/2.59  #Partial instantiations: 0
% 7.97/2.59  #Strategies tried      : 1
% 7.97/2.59  
% 7.97/2.59  Timing (in seconds)
% 7.97/2.59  ----------------------
% 7.97/2.60  Preprocessing        : 0.39
% 7.97/2.60  Parsing              : 0.20
% 7.97/2.60  CNF conversion       : 0.03
% 7.97/2.60  Main loop            : 1.37
% 7.97/2.60  Inferencing          : 0.44
% 7.97/2.60  Reduction            : 0.54
% 7.97/2.60  Demodulation         : 0.41
% 7.97/2.60  BG Simplification    : 0.07
% 7.97/2.60  Subsumption          : 0.24
% 7.97/2.60  Abstraction          : 0.07
% 7.97/2.60  MUC search           : 0.00
% 7.97/2.60  Cooper               : 0.00
% 7.97/2.60  Total                : 1.82
% 7.97/2.60  Index Insertion      : 0.00
% 7.97/2.60  Index Deletion       : 0.00
% 7.97/2.60  Index Matching       : 0.00
% 7.97/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
