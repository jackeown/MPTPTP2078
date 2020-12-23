%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:19 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 295 expanded)
%              Number of leaves         :   50 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 ( 873 expanded)
%              Number of equality atoms :   45 (  82 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_135,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_87,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_103,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_157,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_85,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_148,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_162,plain,(
    ! [B_70,A_71] :
      ( v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_162])).

tff(c_184,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_188,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_184])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_58,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_80,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_1386,plain,(
    ! [B_166,C_163,F_165,A_162,D_164,E_161] :
      ( k1_partfun1(A_162,B_166,C_163,D_164,E_161,F_165) = k5_relat_1(E_161,F_165)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_163,D_164)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_166)))
      | ~ v1_funct_1(E_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1396,plain,(
    ! [A_162,B_166,E_161] :
      ( k1_partfun1(A_162,B_166,'#skF_2','#skF_1',E_161,'#skF_4') = k5_relat_1(E_161,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_166)))
      | ~ v1_funct_1(E_161) ) ),
    inference(resolution,[status(thm)],[c_68,c_1386])).

tff(c_2786,plain,(
    ! [A_217,B_218,E_219] :
      ( k1_partfun1(A_217,B_218,'#skF_2','#skF_1',E_219,'#skF_4') = k5_relat_1(E_219,'#skF_4')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1396])).

tff(c_2816,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2786])).

tff(c_2830,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2816])).

tff(c_52,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3238,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2830,c_52])).

tff(c_3245,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_3238])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_79,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_777,plain,(
    ! [D_125,C_126,A_127,B_128] :
      ( D_125 = C_126
      | ~ r2_relset_1(A_127,B_128,C_126,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_787,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_777])).

tff(c_806,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_787])).

tff(c_911,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_806])).

tff(c_3309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3245,c_2830,c_911])).

tff(c_3310,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_806])).

tff(c_5071,plain,(
    ! [B_312,D_311,E_310,C_314,A_313] :
      ( k1_xboole_0 = C_314
      | v2_funct_1(D_311)
      | ~ v2_funct_1(k1_partfun1(A_313,B_312,B_312,C_314,D_311,E_310))
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(B_312,C_314)))
      | ~ v1_funct_2(E_310,B_312,C_314)
      | ~ v1_funct_1(E_310)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1(A_313,B_312)))
      | ~ v1_funct_2(D_311,A_313,B_312)
      | ~ v1_funct_1(D_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_5075,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3310,c_5071])).

tff(c_5079,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_80,c_5075])).

tff(c_5080,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5079])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [B_72,A_73] :
      ( ~ r1_xboole_0(B_72,A_73)
      | ~ r1_tarski(B_72,A_73)
      | v1_xboole_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_194,plain,(
    ! [A_74] :
      ( ~ r1_tarski(A_74,k1_xboole_0)
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_203,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_5123,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5080,c_203])).

tff(c_5135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_5123])).

tff(c_5136,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5144,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5136,c_2])).

tff(c_94,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_100,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_34])).

tff(c_111,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_80])).

tff(c_5149,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5144,c_111])).

tff(c_5156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5149])).

tff(c_5157,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5274,plain,(
    ! [B_329,A_330] :
      ( v1_relat_1(B_329)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(A_330))
      | ~ v1_relat_1(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5283,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_5274])).

tff(c_5295,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5283])).

tff(c_5485,plain,(
    ! [C_348,B_349,A_350] :
      ( v5_relat_1(C_348,B_349)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5500,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_5485])).

tff(c_5286,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_5274])).

tff(c_5298,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5286])).

tff(c_32,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_81,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_6272,plain,(
    ! [C_407,B_410,F_409,D_408,A_406,E_405] :
      ( k1_partfun1(A_406,B_410,C_407,D_408,E_405,F_409) = k5_relat_1(E_405,F_409)
      | ~ m1_subset_1(F_409,k1_zfmisc_1(k2_zfmisc_1(C_407,D_408)))
      | ~ v1_funct_1(F_409)
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(A_406,B_410)))
      | ~ v1_funct_1(E_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6280,plain,(
    ! [A_406,B_410,E_405] :
      ( k1_partfun1(A_406,B_410,'#skF_2','#skF_1',E_405,'#skF_4') = k5_relat_1(E_405,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(A_406,B_410)))
      | ~ v1_funct_1(E_405) ) ),
    inference(resolution,[status(thm)],[c_68,c_6272])).

tff(c_7313,plain,(
    ! [A_459,B_460,E_461] :
      ( k1_partfun1(A_459,B_460,'#skF_2','#skF_1',E_461,'#skF_4') = k5_relat_1(E_461,'#skF_4')
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460)))
      | ~ v1_funct_1(E_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6280])).

tff(c_7343,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_7313])).

tff(c_7357,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7343])).

tff(c_8266,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7357,c_52])).

tff(c_8272,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_8266])).

tff(c_5757,plain,(
    ! [D_372,C_373,A_374,B_375] :
      ( D_372 = C_373
      | ~ r2_relset_1(A_374,B_375,C_373,D_372)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375)))
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5767,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_5757])).

tff(c_5786,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_5767])).

tff(c_8377,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8272,c_7357,c_7357,c_5786])).

tff(c_28,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8399,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8377,c_28])).

tff(c_8407,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5295,c_81,c_8399])).

tff(c_5303,plain,(
    ! [B_332,A_333] :
      ( r1_tarski(k2_relat_1(B_332),A_333)
      | ~ v5_relat_1(B_332,A_333)
      | ~ v1_relat_1(B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5321,plain,(
    ! [B_332,A_333] :
      ( k2_relat_1(B_332) = A_333
      | ~ r1_tarski(A_333,k2_relat_1(B_332))
      | ~ v5_relat_1(B_332,A_333)
      | ~ v1_relat_1(B_332) ) ),
    inference(resolution,[status(thm)],[c_5303,c_4])).

tff(c_8411,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8407,c_5321])).

tff(c_8416,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_5500,c_8411])).

tff(c_5411,plain,(
    ! [B_338,A_339] :
      ( v5_relat_1(B_338,A_339)
      | ~ r1_tarski(k2_relat_1(B_338),A_339)
      | ~ v1_relat_1(B_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5430,plain,(
    ! [B_338] :
      ( v5_relat_1(B_338,k2_relat_1(B_338))
      | ~ v1_relat_1(B_338) ) ),
    inference(resolution,[status(thm)],[c_8,c_5411])).

tff(c_5525,plain,(
    ! [B_353] :
      ( v2_funct_2(B_353,k2_relat_1(B_353))
      | ~ v5_relat_1(B_353,k2_relat_1(B_353))
      | ~ v1_relat_1(B_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5539,plain,(
    ! [B_338] :
      ( v2_funct_2(B_338,k2_relat_1(B_338))
      | ~ v1_relat_1(B_338) ) ),
    inference(resolution,[status(thm)],[c_5430,c_5525])).

tff(c_8438,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8416,c_5539])).

tff(c_8462,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_8438])).

tff(c_8464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5157,c_8462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.22/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.22/2.49  
% 7.22/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.49  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.36/2.49  
% 7.36/2.49  %Foreground sorts:
% 7.36/2.49  
% 7.36/2.49  
% 7.36/2.49  %Background operators:
% 7.36/2.49  
% 7.36/2.49  
% 7.36/2.49  %Foreground operators:
% 7.36/2.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.36/2.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.36/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.36/2.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.36/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.36/2.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.36/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.36/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.36/2.49  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.36/2.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.36/2.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.36/2.49  tff('#skF_2', type, '#skF_2': $i).
% 7.36/2.49  tff('#skF_3', type, '#skF_3': $i).
% 7.36/2.49  tff('#skF_1', type, '#skF_1': $i).
% 7.36/2.49  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.36/2.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.36/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.36/2.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.36/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.36/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.36/2.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.36/2.49  tff('#skF_4', type, '#skF_4': $i).
% 7.36/2.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.36/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.36/2.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.36/2.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.36/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.36/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.36/2.49  
% 7.36/2.51  tff(f_177, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.36/2.51  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 7.36/2.51  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.36/2.51  tff(f_135, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.36/2.51  tff(f_87, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.36/2.51  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.36/2.51  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.36/2.51  tff(f_103, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.36/2.51  tff(f_101, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.36/2.51  tff(f_157, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 7.36/2.51  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.36/2.51  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.36/2.51  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 7.36/2.51  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.36/2.51  tff(f_85, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 7.36/2.51  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.36/2.51  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.36/2.51  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.36/2.51  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.36/2.51  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 7.36/2.51  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.36/2.51  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.36/2.51  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_148, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 7.36/2.51  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.36/2.51  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_162, plain, (![B_70, A_71]: (v1_xboole_0(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.51  tff(c_178, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_162])).
% 7.36/2.51  tff(c_184, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_178])).
% 7.36/2.51  tff(c_188, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_184])).
% 7.36/2.51  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_58, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.36/2.51  tff(c_36, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.36/2.51  tff(c_80, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 7.36/2.51  tff(c_1386, plain, (![B_166, C_163, F_165, A_162, D_164, E_161]: (k1_partfun1(A_162, B_166, C_163, D_164, E_161, F_165)=k5_relat_1(E_161, F_165) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(C_163, D_164))) | ~v1_funct_1(F_165) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_166))) | ~v1_funct_1(E_161))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.36/2.51  tff(c_1396, plain, (![A_162, B_166, E_161]: (k1_partfun1(A_162, B_166, '#skF_2', '#skF_1', E_161, '#skF_4')=k5_relat_1(E_161, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_166))) | ~v1_funct_1(E_161))), inference(resolution, [status(thm)], [c_68, c_1386])).
% 7.36/2.51  tff(c_2786, plain, (![A_217, B_218, E_219]: (k1_partfun1(A_217, B_218, '#skF_2', '#skF_1', E_219, '#skF_4')=k5_relat_1(E_219, '#skF_4') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_1(E_219))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1396])).
% 7.36/2.51  tff(c_2816, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2786])).
% 7.36/2.51  tff(c_2830, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2816])).
% 7.36/2.51  tff(c_52, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.36/2.51  tff(c_3238, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2830, c_52])).
% 7.36/2.51  tff(c_3245, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_3238])).
% 7.36/2.51  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.36/2.51  tff(c_79, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46])).
% 7.36/2.51  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.36/2.51  tff(c_777, plain, (![D_125, C_126, A_127, B_128]: (D_125=C_126 | ~r2_relset_1(A_127, B_128, C_126, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.36/2.51  tff(c_787, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_777])).
% 7.36/2.51  tff(c_806, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_787])).
% 7.36/2.51  tff(c_911, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_806])).
% 7.36/2.51  tff(c_3309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3245, c_2830, c_911])).
% 7.36/2.51  tff(c_3310, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_806])).
% 7.36/2.51  tff(c_5071, plain, (![B_312, D_311, E_310, C_314, A_313]: (k1_xboole_0=C_314 | v2_funct_1(D_311) | ~v2_funct_1(k1_partfun1(A_313, B_312, B_312, C_314, D_311, E_310)) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(B_312, C_314))) | ~v1_funct_2(E_310, B_312, C_314) | ~v1_funct_1(E_310) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1(A_313, B_312))) | ~v1_funct_2(D_311, A_313, B_312) | ~v1_funct_1(D_311))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.36/2.51  tff(c_5075, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3310, c_5071])).
% 7.36/2.51  tff(c_5079, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_80, c_5075])).
% 7.36/2.51  tff(c_5080, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_148, c_5079])).
% 7.36/2.51  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.36/2.51  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.36/2.51  tff(c_189, plain, (![B_72, A_73]: (~r1_xboole_0(B_72, A_73) | ~r1_tarski(B_72, A_73) | v1_xboole_0(B_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.36/2.51  tff(c_194, plain, (![A_74]: (~r1_tarski(A_74, k1_xboole_0) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_12, c_189])).
% 7.36/2.51  tff(c_203, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_194])).
% 7.36/2.51  tff(c_5123, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5080, c_203])).
% 7.36/2.51  tff(c_5135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_5123])).
% 7.36/2.51  tff(c_5136, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_178])).
% 7.36/2.51  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.36/2.51  tff(c_5144, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5136, c_2])).
% 7.36/2.51  tff(c_94, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.36/2.51  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.36/2.51  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_34])).
% 7.36/2.51  tff(c_111, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_80])).
% 7.36/2.51  tff(c_5149, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5144, c_111])).
% 7.36/2.51  tff(c_5156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_5149])).
% 7.36/2.51  tff(c_5157, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 7.36/2.51  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.36/2.51  tff(c_5274, plain, (![B_329, A_330]: (v1_relat_1(B_329) | ~m1_subset_1(B_329, k1_zfmisc_1(A_330)) | ~v1_relat_1(A_330))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.36/2.51  tff(c_5283, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_5274])).
% 7.36/2.51  tff(c_5295, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5283])).
% 7.36/2.51  tff(c_5485, plain, (![C_348, B_349, A_350]: (v5_relat_1(C_348, B_349) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.36/2.51  tff(c_5500, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_5485])).
% 7.36/2.51  tff(c_5286, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_5274])).
% 7.36/2.51  tff(c_5298, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5286])).
% 7.36/2.51  tff(c_32, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.36/2.51  tff(c_81, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 7.36/2.51  tff(c_6272, plain, (![C_407, B_410, F_409, D_408, A_406, E_405]: (k1_partfun1(A_406, B_410, C_407, D_408, E_405, F_409)=k5_relat_1(E_405, F_409) | ~m1_subset_1(F_409, k1_zfmisc_1(k2_zfmisc_1(C_407, D_408))) | ~v1_funct_1(F_409) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(A_406, B_410))) | ~v1_funct_1(E_405))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.36/2.51  tff(c_6280, plain, (![A_406, B_410, E_405]: (k1_partfun1(A_406, B_410, '#skF_2', '#skF_1', E_405, '#skF_4')=k5_relat_1(E_405, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(A_406, B_410))) | ~v1_funct_1(E_405))), inference(resolution, [status(thm)], [c_68, c_6272])).
% 7.36/2.51  tff(c_7313, plain, (![A_459, B_460, E_461]: (k1_partfun1(A_459, B_460, '#skF_2', '#skF_1', E_461, '#skF_4')=k5_relat_1(E_461, '#skF_4') | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))) | ~v1_funct_1(E_461))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6280])).
% 7.36/2.51  tff(c_7343, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_7313])).
% 7.36/2.51  tff(c_7357, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7343])).
% 7.36/2.51  tff(c_8266, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7357, c_52])).
% 7.36/2.51  tff(c_8272, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_8266])).
% 7.36/2.51  tff(c_5757, plain, (![D_372, C_373, A_374, B_375]: (D_372=C_373 | ~r2_relset_1(A_374, B_375, C_373, D_372) | ~m1_subset_1(D_372, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.36/2.51  tff(c_5767, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_5757])).
% 7.36/2.51  tff(c_5786, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_5767])).
% 7.36/2.51  tff(c_8377, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8272, c_7357, c_7357, c_5786])).
% 7.36/2.51  tff(c_28, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.36/2.51  tff(c_8399, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8377, c_28])).
% 7.36/2.51  tff(c_8407, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5295, c_81, c_8399])).
% 7.36/2.51  tff(c_5303, plain, (![B_332, A_333]: (r1_tarski(k2_relat_1(B_332), A_333) | ~v5_relat_1(B_332, A_333) | ~v1_relat_1(B_332))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.36/2.51  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.36/2.51  tff(c_5321, plain, (![B_332, A_333]: (k2_relat_1(B_332)=A_333 | ~r1_tarski(A_333, k2_relat_1(B_332)) | ~v5_relat_1(B_332, A_333) | ~v1_relat_1(B_332))), inference(resolution, [status(thm)], [c_5303, c_4])).
% 7.36/2.51  tff(c_8411, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8407, c_5321])).
% 7.36/2.51  tff(c_8416, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_5500, c_8411])).
% 7.36/2.51  tff(c_5411, plain, (![B_338, A_339]: (v5_relat_1(B_338, A_339) | ~r1_tarski(k2_relat_1(B_338), A_339) | ~v1_relat_1(B_338))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.36/2.51  tff(c_5430, plain, (![B_338]: (v5_relat_1(B_338, k2_relat_1(B_338)) | ~v1_relat_1(B_338))), inference(resolution, [status(thm)], [c_8, c_5411])).
% 7.36/2.51  tff(c_5525, plain, (![B_353]: (v2_funct_2(B_353, k2_relat_1(B_353)) | ~v5_relat_1(B_353, k2_relat_1(B_353)) | ~v1_relat_1(B_353))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.36/2.51  tff(c_5539, plain, (![B_338]: (v2_funct_2(B_338, k2_relat_1(B_338)) | ~v1_relat_1(B_338))), inference(resolution, [status(thm)], [c_5430, c_5525])).
% 7.36/2.51  tff(c_8438, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8416, c_5539])).
% 7.36/2.51  tff(c_8462, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_8438])).
% 7.36/2.51  tff(c_8464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5157, c_8462])).
% 7.36/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.51  
% 7.36/2.51  Inference rules
% 7.36/2.51  ----------------------
% 7.36/2.51  #Ref     : 0
% 7.36/2.51  #Sup     : 1947
% 7.36/2.51  #Fact    : 0
% 7.36/2.51  #Define  : 0
% 7.36/2.51  #Split   : 15
% 7.36/2.51  #Chain   : 0
% 7.36/2.51  #Close   : 0
% 7.36/2.51  
% 7.36/2.51  Ordering : KBO
% 7.36/2.51  
% 7.36/2.51  Simplification rules
% 7.36/2.51  ----------------------
% 7.36/2.51  #Subsume      : 180
% 7.36/2.51  #Demod        : 2158
% 7.36/2.51  #Tautology    : 1101
% 7.36/2.51  #SimpNegUnit  : 6
% 7.36/2.51  #BackRed      : 84
% 7.36/2.51  
% 7.36/2.51  #Partial instantiations: 0
% 7.36/2.51  #Strategies tried      : 1
% 7.36/2.51  
% 7.36/2.51  Timing (in seconds)
% 7.36/2.51  ----------------------
% 7.36/2.51  Preprocessing        : 0.36
% 7.36/2.51  Parsing              : 0.19
% 7.36/2.51  CNF conversion       : 0.03
% 7.36/2.51  Main loop            : 1.36
% 7.36/2.51  Inferencing          : 0.45
% 7.36/2.51  Reduction            : 0.50
% 7.36/2.51  Demodulation         : 0.36
% 7.36/2.51  BG Simplification    : 0.05
% 7.36/2.51  Subsumption          : 0.26
% 7.36/2.51  Abstraction          : 0.06
% 7.36/2.51  MUC search           : 0.00
% 7.36/2.51  Cooper               : 0.00
% 7.36/2.51  Total                : 1.77
% 7.36/2.51  Index Insertion      : 0.00
% 7.36/2.52  Index Deletion       : 0.00
% 7.36/2.52  Index Matching       : 0.00
% 7.36/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
