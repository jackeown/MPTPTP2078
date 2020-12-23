%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:53 EST 2020

% Result     : Theorem 9.76s
% Output     : CNFRefutation 9.97s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 792 expanded)
%              Number of leaves         :   63 ( 305 expanded)
%              Depth                    :   17
%              Number of atoms          :  367 (2659 expanded)
%              Number of equality atoms :   69 ( 236 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_funct_2 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k3_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_253,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_186,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_114,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_158,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_231,axiom,(
    ! [A,B,C] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_184,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_174,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_126,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
       => r2_relset_1(A,B,D,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_277,plain,(
    ! [A_126,B_127,D_128] :
      ( r2_relset_1(A_126,B_127,D_128,D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_285,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_277])).

tff(c_143,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_143])).

tff(c_195,plain,(
    ! [C_108,A_109,B_110] :
      ( v4_relat_1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_206,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_195])).

tff(c_163,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_174,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_163])).

tff(c_288,plain,(
    ! [B_130,A_131] :
      ( k2_relat_1(B_130) = A_131
      | ~ v2_funct_2(B_130,A_131)
      | ~ v5_relat_1(B_130,A_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_297,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_2('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_288])).

tff(c_306,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_2('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_297])).

tff(c_811,plain,(
    ~ v2_funct_2('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_94,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_90,plain,(
    v3_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_1064,plain,(
    ! [C_189,B_190,A_191] :
      ( v2_funct_2(C_189,B_190)
      | ~ v3_funct_2(C_189,A_191,B_190)
      | ~ v1_funct_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1070,plain,
    ( v2_funct_2('#skF_5','#skF_3')
    | ~ v3_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_1064])).

tff(c_1077,plain,(
    v2_funct_2('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_1070])).

tff(c_1079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_1077])).

tff(c_1080,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_22,plain,(
    ! [A_15] :
      ( k2_xboole_0(k1_relat_1(A_15),k2_relat_1(A_15)) = k3_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1088,plain,
    ( k2_xboole_0(k1_relat_1('#skF_5'),'#skF_3') = k3_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_22])).

tff(c_1094,plain,(
    k2_xboole_0(k1_relat_1('#skF_5'),'#skF_3') = k3_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1088])).

tff(c_186,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(k1_relat_1(B_106),A_107)
      | ~ v4_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [B_106,A_107] :
      ( k2_xboole_0(k1_relat_1(B_106),A_107) = A_107
      | ~ v4_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_186,c_4])).

tff(c_1136,plain,
    ( k3_relat_1('#skF_5') = '#skF_3'
    | ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_194])).

tff(c_1143,plain,(
    k3_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_206,c_1136])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1202,plain,(
    ! [C_197,A_198,B_199] :
      ( r1_tarski(k3_relat_1(C_197),k2_xboole_0(A_198,B_199))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1236,plain,(
    ! [C_200,A_201] :
      ( r1_tarski(k3_relat_1(C_200),A_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_201,A_201))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1202])).

tff(c_1242,plain,(
    r1_tarski(k3_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_1236])).

tff(c_1248,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1242])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1290,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1248,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    ! [B_97,A_98] :
      ( ~ r1_xboole_0(B_97,A_98)
      | ~ r1_tarski(B_97,A_98)
      | v1_xboole_0(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [A_114,B_115] :
      ( ~ r1_tarski(A_114,B_115)
      | v1_xboole_0(A_114)
      | k4_xboole_0(A_114,B_115) != A_114 ) ),
    inference(resolution,[status(thm)],[c_16,c_157])).

tff(c_227,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | k4_xboole_0(A_5,B_6) != A_5
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_1304,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 != '#skF_3'
    | k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_227])).

tff(c_1311,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1304])).

tff(c_1315,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1311])).

tff(c_102,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_100,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_92,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_143])).

tff(c_175,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_163])).

tff(c_294,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_2('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_288])).

tff(c_303,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_294])).

tff(c_307,plain,(
    ~ v2_funct_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_98,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_775,plain,(
    ! [C_168,B_169,A_170] :
      ( v2_funct_2(C_168,B_169)
      | ~ v3_funct_2(C_168,A_170,B_169)
      | ~ v1_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_784,plain,
    ( v2_funct_2('#skF_4','#skF_3')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_775])).

tff(c_791,plain,(
    v2_funct_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_784])).

tff(c_793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_791])).

tff(c_794,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_1152,plain,(
    ! [A_192,B_193,C_194] :
      ( k2_relset_1(A_192,B_193,C_194) = k2_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1161,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_1152])).

tff(c_1166,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_1161])).

tff(c_76,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_46,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_103,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_284,plain,(
    ! [A_38] : r2_relset_1(A_38,A_38,k6_partfun1(A_38),k6_partfun1(A_38)) ),
    inference(resolution,[status(thm)],[c_103,c_277])).

tff(c_1251,plain,(
    ! [C_202,A_203,B_204] :
      ( v2_funct_1(C_202)
      | ~ v3_funct_2(C_202,A_203,B_204)
      | ~ v1_funct_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1260,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_1251])).

tff(c_1267,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_1260])).

tff(c_2604,plain,(
    ! [B_292,C_293,A_291,F_296,D_294,E_295] :
      ( m1_subset_1(k1_partfun1(A_291,B_292,C_293,D_294,E_295,F_296),k1_zfmisc_1(k2_zfmisc_1(A_291,D_294)))
      | ~ m1_subset_1(F_296,k1_zfmisc_1(k2_zfmisc_1(C_293,D_294)))
      | ~ v1_funct_1(F_296)
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(E_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_86,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_1384,plain,(
    ! [D_216,C_217,A_218,B_219] :
      ( D_216 = C_217
      | ~ r2_relset_1(A_218,B_219,C_217,D_216)
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1392,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_86,c_1384])).

tff(c_1407,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1392])).

tff(c_1416,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1407])).

tff(c_2655,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2604,c_1416])).

tff(c_2705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_96,c_94,c_88,c_2655])).

tff(c_2706,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1407])).

tff(c_8024,plain,(
    ! [C_564,D_565,B_566,A_567] :
      ( k2_funct_1(C_564) = D_565
      | k1_xboole_0 = B_566
      | k1_xboole_0 = A_567
      | ~ v2_funct_1(C_564)
      | ~ r2_relset_1(A_567,A_567,k1_partfun1(A_567,B_566,B_566,A_567,C_564,D_565),k6_partfun1(A_567))
      | k2_relset_1(A_567,B_566,C_564) != B_566
      | ~ m1_subset_1(D_565,k1_zfmisc_1(k2_zfmisc_1(B_566,A_567)))
      | ~ v1_funct_2(D_565,B_566,A_567)
      | ~ v1_funct_1(D_565)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(A_567,B_566)))
      | ~ v1_funct_2(C_564,A_567,B_566)
      | ~ v1_funct_1(C_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_8027,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2706,c_8024])).

tff(c_8029,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_96,c_94,c_92,c_88,c_1166,c_284,c_1267,c_8027])).

tff(c_8030,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1315,c_8029])).

tff(c_2745,plain,(
    ! [A_302,B_303] :
      ( k2_funct_2(A_302,B_303) = k2_funct_1(B_303)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(k2_zfmisc_1(A_302,A_302)))
      | ~ v3_funct_2(B_303,A_302,A_302)
      | ~ v1_funct_2(B_303,A_302,A_302)
      | ~ v1_funct_1(B_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2754,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_2745])).

tff(c_2761,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_2754])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_2768,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2761,c_84])).

tff(c_4880,plain,(
    ! [A_422,B_423] :
      ( m1_subset_1(k2_funct_2(A_422,B_423),k1_zfmisc_1(k2_zfmisc_1(A_422,A_422)))
      | ~ m1_subset_1(B_423,k1_zfmisc_1(k2_zfmisc_1(A_422,A_422)))
      | ~ v3_funct_2(B_423,A_422,A_422)
      | ~ v1_funct_2(B_423,A_422,A_422)
      | ~ v1_funct_1(B_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_4936,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2761,c_4880])).

tff(c_4961,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_96,c_4936])).

tff(c_2889,plain,(
    ! [A_328,B_329,C_330] :
      ( r2_hidden('#skF_1'(A_328,B_329,C_330),A_328)
      | r2_relset_1(A_328,A_328,B_329,C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_328,A_328)))
      | ~ m1_subset_1(B_329,k1_zfmisc_1(k2_zfmisc_1(A_328,A_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2897,plain,(
    ! [B_329] :
      ( r2_hidden('#skF_1'('#skF_3',B_329,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_329,'#skF_5')
      | ~ m1_subset_1(B_329,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_88,c_2889])).

tff(c_5011,plain,
    ( r2_hidden('#skF_1'('#skF_3',k2_funct_1('#skF_4'),'#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4961,c_2897])).

tff(c_7551,plain,(
    r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5011])).

tff(c_42,plain,(
    ! [A_31,B_32,D_34,C_33] :
      ( r2_relset_1(A_31,B_32,D_34,C_33)
      | ~ r2_relset_1(A_31,B_32,C_33,D_34)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7566,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_7551,c_42])).

tff(c_7571,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4961,c_88,c_7566])).

tff(c_7573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2768,c_7571])).

tff(c_7575,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5011])).

tff(c_8038,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8030,c_7575])).

tff(c_8061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_8038])).

tff(c_8062,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1311])).

tff(c_9682,plain,(
    ! [A_711,B_712,C_713] :
      ( r2_hidden('#skF_1'(A_711,B_712,C_713),A_711)
      | r2_relset_1(A_711,A_711,B_712,C_713)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(A_711,A_711)))
      | ~ m1_subset_1(B_712,k1_zfmisc_1(k2_zfmisc_1(A_711,A_711))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_9742,plain,(
    ! [B_726] :
      ( r2_hidden('#skF_1'('#skF_3',B_726,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_726,'#skF_5')
      | ~ m1_subset_1(B_726,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_88,c_9682])).

tff(c_9756,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_9742])).

tff(c_9757,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9756])).

tff(c_40,plain,(
    ! [D_30,C_29,A_27,B_28] :
      ( D_30 = C_29
      | ~ r2_relset_1(A_27,B_28,C_29,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9761,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_9757,c_40])).

tff(c_9767,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_88,c_9761])).

tff(c_9551,plain,(
    ! [A_686,B_687] :
      ( k2_funct_2(A_686,B_687) = k2_funct_1(B_687)
      | ~ m1_subset_1(B_687,k1_zfmisc_1(k2_zfmisc_1(A_686,A_686)))
      | ~ v3_funct_2(B_687,A_686,A_686)
      | ~ v1_funct_2(B_687,A_686,A_686)
      | ~ v1_funct_1(B_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_9560,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_9551])).

tff(c_9567,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_9560])).

tff(c_9574,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9567,c_84])).

tff(c_9775,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9767,c_9574])).

tff(c_9821,plain,(
    ! [A_727,B_728] :
      ( m1_subset_1(k2_funct_2(A_727,B_728),k1_zfmisc_1(k2_zfmisc_1(A_727,A_727)))
      | ~ m1_subset_1(B_728,k1_zfmisc_1(k2_zfmisc_1(A_727,A_727)))
      | ~ v3_funct_2(B_728,A_727,A_727)
      | ~ v1_funct_2(B_728,A_727,A_727)
      | ~ v1_funct_1(B_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_9871,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9567,c_9821])).

tff(c_9892,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_96,c_9871])).

tff(c_9974,plain,(
    ! [B_729] :
      ( r2_hidden('#skF_1'('#skF_3',B_729,'#skF_4'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_729,'#skF_4')
      | ~ m1_subset_1(B_729,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_96,c_9682])).

tff(c_9989,plain,
    ( r2_hidden('#skF_1'('#skF_3',k2_funct_1('#skF_4'),'#skF_4'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9892,c_9974])).

tff(c_10364,plain,(
    r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_9989])).

tff(c_10372,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10364,c_42])).

tff(c_10377,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9892,c_96,c_10372])).

tff(c_10379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9775,c_10377])).

tff(c_10380,plain,(
    r2_hidden('#skF_1'('#skF_3',k2_funct_1('#skF_4'),'#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_9989])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10407,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10380,c_12])).

tff(c_10411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8062,c_10407])).

tff(c_10412,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_9756])).

tff(c_10416,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10412,c_12])).

tff(c_10420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8062,c_10416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.76/3.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.76/3.41  
% 9.76/3.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.76/3.41  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_funct_2 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k3_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.76/3.41  
% 9.76/3.41  %Foreground sorts:
% 9.76/3.41  
% 9.76/3.41  
% 9.76/3.41  %Background operators:
% 9.76/3.41  
% 9.76/3.41  
% 9.76/3.41  %Foreground operators:
% 9.76/3.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.76/3.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.76/3.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.76/3.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.76/3.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.76/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.76/3.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.76/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.76/3.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.76/3.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.76/3.41  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 9.76/3.41  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.76/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.76/3.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.76/3.41  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.76/3.41  tff('#skF_5', type, '#skF_5': $i).
% 9.76/3.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.76/3.41  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 9.76/3.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.76/3.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.76/3.41  tff('#skF_3', type, '#skF_3': $i).
% 9.76/3.41  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.76/3.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.76/3.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.76/3.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.76/3.41  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.76/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.76/3.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.76/3.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.76/3.41  tff('#skF_4', type, '#skF_4': $i).
% 9.76/3.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.76/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.76/3.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.76/3.41  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.76/3.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.76/3.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.76/3.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.76/3.41  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 9.76/3.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.76/3.41  
% 9.97/3.45  tff(f_253, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 9.97/3.45  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.97/3.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.97/3.45  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.97/3.45  tff(f_146, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.97/3.45  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.97/3.45  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 9.97/3.45  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.97/3.45  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.97/3.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.97/3.45  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 9.97/3.45  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 9.97/3.45  tff(f_52, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.97/3.45  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 9.97/3.45  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.97/3.45  tff(f_186, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.97/3.45  tff(f_114, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.97/3.45  tff(f_158, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.97/3.45  tff(f_231, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.97/3.45  tff(f_184, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.97/3.45  tff(f_174, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 9.97/3.45  tff(f_126, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 9.97/3.45  tff(f_108, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) => r2_relset_1(A, B, D, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r2_relset_1)).
% 9.97/3.45  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 9.97/3.45  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_277, plain, (![A_126, B_127, D_128]: (r2_relset_1(A_126, B_127, D_128, D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.97/3.45  tff(c_285, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_88, c_277])).
% 9.97/3.45  tff(c_143, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.97/3.45  tff(c_154, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_143])).
% 9.97/3.45  tff(c_195, plain, (![C_108, A_109, B_110]: (v4_relat_1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.97/3.45  tff(c_206, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_195])).
% 9.97/3.45  tff(c_163, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.97/3.45  tff(c_174, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_163])).
% 9.97/3.45  tff(c_288, plain, (![B_130, A_131]: (k2_relat_1(B_130)=A_131 | ~v2_funct_2(B_130, A_131) | ~v5_relat_1(B_130, A_131) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.97/3.45  tff(c_297, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v2_funct_2('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_174, c_288])).
% 9.97/3.45  tff(c_306, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v2_funct_2('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_297])).
% 9.97/3.45  tff(c_811, plain, (~v2_funct_2('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_306])).
% 9.97/3.45  tff(c_94, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_90, plain, (v3_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_1064, plain, (![C_189, B_190, A_191]: (v2_funct_2(C_189, B_190) | ~v3_funct_2(C_189, A_191, B_190) | ~v1_funct_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.97/3.45  tff(c_1070, plain, (v2_funct_2('#skF_5', '#skF_3') | ~v3_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_1064])).
% 9.97/3.45  tff(c_1077, plain, (v2_funct_2('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_1070])).
% 9.97/3.45  tff(c_1079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_811, c_1077])).
% 9.97/3.45  tff(c_1080, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_306])).
% 9.97/3.45  tff(c_22, plain, (![A_15]: (k2_xboole_0(k1_relat_1(A_15), k2_relat_1(A_15))=k3_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.97/3.45  tff(c_1088, plain, (k2_xboole_0(k1_relat_1('#skF_5'), '#skF_3')=k3_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1080, c_22])).
% 9.97/3.45  tff(c_1094, plain, (k2_xboole_0(k1_relat_1('#skF_5'), '#skF_3')=k3_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1088])).
% 9.97/3.45  tff(c_186, plain, (![B_106, A_107]: (r1_tarski(k1_relat_1(B_106), A_107) | ~v4_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.97/3.45  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.97/3.45  tff(c_194, plain, (![B_106, A_107]: (k2_xboole_0(k1_relat_1(B_106), A_107)=A_107 | ~v4_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_186, c_4])).
% 9.97/3.45  tff(c_1136, plain, (k3_relat_1('#skF_5')='#skF_3' | ~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1094, c_194])).
% 9.97/3.45  tff(c_1143, plain, (k3_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_206, c_1136])).
% 9.97/3.45  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.97/3.45  tff(c_1202, plain, (![C_197, A_198, B_199]: (r1_tarski(k3_relat_1(C_197), k2_xboole_0(A_198, B_199)) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.97/3.45  tff(c_1236, plain, (![C_200, A_201]: (r1_tarski(k3_relat_1(C_200), A_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_201, A_201))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1202])).
% 9.97/3.45  tff(c_1242, plain, (r1_tarski(k3_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_88, c_1236])).
% 9.97/3.45  tff(c_1248, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1242])).
% 9.97/3.45  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.97/3.45  tff(c_1290, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1248, c_8])).
% 9.97/3.45  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.97/3.45  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.97/3.45  tff(c_157, plain, (![B_97, A_98]: (~r1_xboole_0(B_97, A_98) | ~r1_tarski(B_97, A_98) | v1_xboole_0(B_97))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.97/3.45  tff(c_219, plain, (![A_114, B_115]: (~r1_tarski(A_114, B_115) | v1_xboole_0(A_114) | k4_xboole_0(A_114, B_115)!=A_114)), inference(resolution, [status(thm)], [c_16, c_157])).
% 9.97/3.45  tff(c_227, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | k4_xboole_0(A_5, B_6)!=A_5 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_219])).
% 9.97/3.45  tff(c_1304, plain, (v1_xboole_0('#skF_3') | k1_xboole_0!='#skF_3' | k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1290, c_227])).
% 9.97/3.45  tff(c_1311, plain, (v1_xboole_0('#skF_3') | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1304])).
% 9.97/3.45  tff(c_1315, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_1311])).
% 9.97/3.45  tff(c_102, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_100, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_92, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_143])).
% 9.97/3.45  tff(c_175, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_163])).
% 9.97/3.45  tff(c_294, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_2('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_175, c_288])).
% 9.97/3.45  tff(c_303, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_294])).
% 9.97/3.45  tff(c_307, plain, (~v2_funct_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_303])).
% 9.97/3.45  tff(c_98, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_775, plain, (![C_168, B_169, A_170]: (v2_funct_2(C_168, B_169) | ~v3_funct_2(C_168, A_170, B_169) | ~v1_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.97/3.45  tff(c_784, plain, (v2_funct_2('#skF_4', '#skF_3') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_775])).
% 9.97/3.45  tff(c_791, plain, (v2_funct_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_784])).
% 9.97/3.45  tff(c_793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_791])).
% 9.97/3.45  tff(c_794, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_303])).
% 9.97/3.45  tff(c_1152, plain, (![A_192, B_193, C_194]: (k2_relset_1(A_192, B_193, C_194)=k2_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.97/3.45  tff(c_1161, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_1152])).
% 9.97/3.45  tff(c_1166, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_794, c_1161])).
% 9.97/3.45  tff(c_76, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.97/3.45  tff(c_46, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.97/3.45  tff(c_103, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46])).
% 9.97/3.45  tff(c_284, plain, (![A_38]: (r2_relset_1(A_38, A_38, k6_partfun1(A_38), k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_103, c_277])).
% 9.97/3.45  tff(c_1251, plain, (![C_202, A_203, B_204]: (v2_funct_1(C_202) | ~v3_funct_2(C_202, A_203, B_204) | ~v1_funct_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.97/3.45  tff(c_1260, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_1251])).
% 9.97/3.45  tff(c_1267, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_1260])).
% 9.97/3.45  tff(c_2604, plain, (![B_292, C_293, A_291, F_296, D_294, E_295]: (m1_subset_1(k1_partfun1(A_291, B_292, C_293, D_294, E_295, F_296), k1_zfmisc_1(k2_zfmisc_1(A_291, D_294))) | ~m1_subset_1(F_296, k1_zfmisc_1(k2_zfmisc_1(C_293, D_294))) | ~v1_funct_1(F_296) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(E_295))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.97/3.45  tff(c_86, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_1384, plain, (![D_216, C_217, A_218, B_219]: (D_216=C_217 | ~r2_relset_1(A_218, B_219, C_217, D_216) | ~m1_subset_1(D_216, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.97/3.45  tff(c_1392, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_86, c_1384])).
% 9.97/3.45  tff(c_1407, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1392])).
% 9.97/3.45  tff(c_1416, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1407])).
% 9.97/3.45  tff(c_2655, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2604, c_1416])).
% 9.97/3.45  tff(c_2705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_96, c_94, c_88, c_2655])).
% 9.97/3.45  tff(c_2706, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1407])).
% 9.97/3.45  tff(c_8024, plain, (![C_564, D_565, B_566, A_567]: (k2_funct_1(C_564)=D_565 | k1_xboole_0=B_566 | k1_xboole_0=A_567 | ~v2_funct_1(C_564) | ~r2_relset_1(A_567, A_567, k1_partfun1(A_567, B_566, B_566, A_567, C_564, D_565), k6_partfun1(A_567)) | k2_relset_1(A_567, B_566, C_564)!=B_566 | ~m1_subset_1(D_565, k1_zfmisc_1(k2_zfmisc_1(B_566, A_567))) | ~v1_funct_2(D_565, B_566, A_567) | ~v1_funct_1(D_565) | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(A_567, B_566))) | ~v1_funct_2(C_564, A_567, B_566) | ~v1_funct_1(C_564))), inference(cnfTransformation, [status(thm)], [f_231])).
% 9.97/3.45  tff(c_8027, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2706, c_8024])).
% 9.97/3.45  tff(c_8029, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_96, c_94, c_92, c_88, c_1166, c_284, c_1267, c_8027])).
% 9.97/3.45  tff(c_8030, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1315, c_8029])).
% 9.97/3.45  tff(c_2745, plain, (![A_302, B_303]: (k2_funct_2(A_302, B_303)=k2_funct_1(B_303) | ~m1_subset_1(B_303, k1_zfmisc_1(k2_zfmisc_1(A_302, A_302))) | ~v3_funct_2(B_303, A_302, A_302) | ~v1_funct_2(B_303, A_302, A_302) | ~v1_funct_1(B_303))), inference(cnfTransformation, [status(thm)], [f_184])).
% 9.97/3.45  tff(c_2754, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_2745])).
% 9.97/3.45  tff(c_2761, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_2754])).
% 9.97/3.45  tff(c_84, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.97/3.45  tff(c_2768, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2761, c_84])).
% 9.97/3.45  tff(c_4880, plain, (![A_422, B_423]: (m1_subset_1(k2_funct_2(A_422, B_423), k1_zfmisc_1(k2_zfmisc_1(A_422, A_422))) | ~m1_subset_1(B_423, k1_zfmisc_1(k2_zfmisc_1(A_422, A_422))) | ~v3_funct_2(B_423, A_422, A_422) | ~v1_funct_2(B_423, A_422, A_422) | ~v1_funct_1(B_423))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.97/3.45  tff(c_4936, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2761, c_4880])).
% 9.97/3.45  tff(c_4961, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_96, c_4936])).
% 9.97/3.45  tff(c_2889, plain, (![A_328, B_329, C_330]: (r2_hidden('#skF_1'(A_328, B_329, C_330), A_328) | r2_relset_1(A_328, A_328, B_329, C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_328, A_328))) | ~m1_subset_1(B_329, k1_zfmisc_1(k2_zfmisc_1(A_328, A_328))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.97/3.45  tff(c_2897, plain, (![B_329]: (r2_hidden('#skF_1'('#skF_3', B_329, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_329, '#skF_5') | ~m1_subset_1(B_329, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_88, c_2889])).
% 9.97/3.45  tff(c_5011, plain, (r2_hidden('#skF_1'('#skF_3', k2_funct_1('#skF_4'), '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_4961, c_2897])).
% 9.97/3.45  tff(c_7551, plain, (r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5011])).
% 9.97/3.45  tff(c_42, plain, (![A_31, B_32, D_34, C_33]: (r2_relset_1(A_31, B_32, D_34, C_33) | ~r2_relset_1(A_31, B_32, C_33, D_34) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.97/3.45  tff(c_7566, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_7551, c_42])).
% 9.97/3.45  tff(c_7571, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4961, c_88, c_7566])).
% 9.97/3.45  tff(c_7573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2768, c_7571])).
% 9.97/3.45  tff(c_7575, plain, (~r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_5011])).
% 9.97/3.45  tff(c_8038, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8030, c_7575])).
% 9.97/3.45  tff(c_8061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_8038])).
% 9.97/3.45  tff(c_8062, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1311])).
% 9.97/3.45  tff(c_9682, plain, (![A_711, B_712, C_713]: (r2_hidden('#skF_1'(A_711, B_712, C_713), A_711) | r2_relset_1(A_711, A_711, B_712, C_713) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(A_711, A_711))) | ~m1_subset_1(B_712, k1_zfmisc_1(k2_zfmisc_1(A_711, A_711))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.97/3.45  tff(c_9742, plain, (![B_726]: (r2_hidden('#skF_1'('#skF_3', B_726, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_726, '#skF_5') | ~m1_subset_1(B_726, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_88, c_9682])).
% 9.97/3.45  tff(c_9756, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_96, c_9742])).
% 9.97/3.45  tff(c_9757, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_9756])).
% 9.97/3.45  tff(c_40, plain, (![D_30, C_29, A_27, B_28]: (D_30=C_29 | ~r2_relset_1(A_27, B_28, C_29, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.97/3.45  tff(c_9761, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_9757, c_40])).
% 9.97/3.45  tff(c_9767, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_88, c_9761])).
% 9.97/3.45  tff(c_9551, plain, (![A_686, B_687]: (k2_funct_2(A_686, B_687)=k2_funct_1(B_687) | ~m1_subset_1(B_687, k1_zfmisc_1(k2_zfmisc_1(A_686, A_686))) | ~v3_funct_2(B_687, A_686, A_686) | ~v1_funct_2(B_687, A_686, A_686) | ~v1_funct_1(B_687))), inference(cnfTransformation, [status(thm)], [f_184])).
% 9.97/3.45  tff(c_9560, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_9551])).
% 9.97/3.45  tff(c_9567, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_9560])).
% 9.97/3.45  tff(c_9574, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9567, c_84])).
% 9.97/3.45  tff(c_9775, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9767, c_9574])).
% 9.97/3.45  tff(c_9821, plain, (![A_727, B_728]: (m1_subset_1(k2_funct_2(A_727, B_728), k1_zfmisc_1(k2_zfmisc_1(A_727, A_727))) | ~m1_subset_1(B_728, k1_zfmisc_1(k2_zfmisc_1(A_727, A_727))) | ~v3_funct_2(B_728, A_727, A_727) | ~v1_funct_2(B_728, A_727, A_727) | ~v1_funct_1(B_728))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.97/3.45  tff(c_9871, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9567, c_9821])).
% 9.97/3.45  tff(c_9892, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_96, c_9871])).
% 9.97/3.45  tff(c_9974, plain, (![B_729]: (r2_hidden('#skF_1'('#skF_3', B_729, '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_729, '#skF_4') | ~m1_subset_1(B_729, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_96, c_9682])).
% 9.97/3.45  tff(c_9989, plain, (r2_hidden('#skF_1'('#skF_3', k2_funct_1('#skF_4'), '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9892, c_9974])).
% 9.97/3.45  tff(c_10364, plain, (r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_9989])).
% 9.97/3.45  tff(c_10372, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_10364, c_42])).
% 9.97/3.45  tff(c_10377, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9892, c_96, c_10372])).
% 9.97/3.45  tff(c_10379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9775, c_10377])).
% 9.97/3.45  tff(c_10380, plain, (r2_hidden('#skF_1'('#skF_3', k2_funct_1('#skF_4'), '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_9989])).
% 9.97/3.45  tff(c_12, plain, (![B_10, A_9]: (~v1_xboole_0(B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.97/3.45  tff(c_10407, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10380, c_12])).
% 9.97/3.45  tff(c_10411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8062, c_10407])).
% 9.97/3.45  tff(c_10412, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_9756])).
% 9.97/3.45  tff(c_10416, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10412, c_12])).
% 9.97/3.45  tff(c_10420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8062, c_10416])).
% 9.97/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.97/3.45  
% 9.97/3.45  Inference rules
% 9.97/3.46  ----------------------
% 9.97/3.46  #Ref     : 17
% 9.97/3.46  #Sup     : 2151
% 9.97/3.46  #Fact    : 0
% 9.97/3.46  #Define  : 0
% 9.97/3.46  #Split   : 54
% 9.97/3.46  #Chain   : 0
% 9.97/3.46  #Close   : 0
% 9.97/3.46  
% 9.97/3.46  Ordering : KBO
% 9.97/3.46  
% 9.97/3.46  Simplification rules
% 9.97/3.46  ----------------------
% 9.97/3.46  #Subsume      : 128
% 9.97/3.46  #Demod        : 3239
% 9.97/3.46  #Tautology    : 1070
% 9.97/3.46  #SimpNegUnit  : 40
% 9.97/3.46  #BackRed      : 559
% 9.97/3.46  
% 9.97/3.46  #Partial instantiations: 0
% 9.97/3.46  #Strategies tried      : 1
% 9.97/3.46  
% 9.97/3.46  Timing (in seconds)
% 9.97/3.46  ----------------------
% 9.97/3.46  Preprocessing        : 0.41
% 9.97/3.46  Parsing              : 0.22
% 9.97/3.46  CNF conversion       : 0.03
% 9.97/3.46  Main loop            : 2.24
% 9.97/3.46  Inferencing          : 0.71
% 9.97/3.46  Reduction            : 0.86
% 9.97/3.46  Demodulation         : 0.63
% 9.97/3.46  BG Simplification    : 0.07
% 9.97/3.46  Subsumption          : 0.41
% 9.97/3.46  Abstraction          : 0.08
% 9.97/3.46  MUC search           : 0.00
% 9.97/3.46  Cooper               : 0.00
% 9.97/3.46  Total                : 2.72
% 9.97/3.46  Index Insertion      : 0.00
% 9.97/3.46  Index Deletion       : 0.00
% 9.97/3.46  Index Matching       : 0.00
% 9.97/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
