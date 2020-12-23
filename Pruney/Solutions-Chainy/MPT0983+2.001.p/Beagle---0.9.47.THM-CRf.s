%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 362 expanded)
%              Number of leaves         :   51 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  295 (1006 expanded)
%              Number of equality atoms :   59 ( 159 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_243,negated_conjecture,(
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

tff(f_129,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_201,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_113,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_199,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_181,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_157,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_177,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_223,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_189,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v1_xboole_0(k6_relat_1(A))
        & v1_relat_1(k6_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_101,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_112,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_10698,plain,(
    ! [A_506] :
      ( v2_funct_1(A_506)
      | ~ v1_funct_1(A_506)
      | ~ v1_relat_1(A_506)
      | ~ v1_xboole_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_98,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_167,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_10701,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10698,c_167])).

tff(c_10704,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_10701])).

tff(c_10705,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10704])).

tff(c_92,plain,(
    ! [A_58] : k6_relat_1(A_58) = k6_partfun1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_42,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_122,plain,(
    ! [A_27] : k1_relat_1(k6_partfun1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_42])).

tff(c_60,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_116,plain,(
    ! [A_31] : v1_relat_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_60])).

tff(c_321,plain,(
    ! [A_100] :
      ( k1_relat_1(A_100) != k1_xboole_0
      | k1_xboole_0 = A_100
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_333,plain,(
    ! [A_31] :
      ( k1_relat_1(k6_partfun1(A_31)) != k1_xboole_0
      | k6_partfun1(A_31) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_116,c_321])).

tff(c_342,plain,(
    ! [A_101] :
      ( k1_xboole_0 != A_101
      | k6_partfun1(A_101) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_333])).

tff(c_100,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_351,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_100])).

tff(c_440,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_110,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_108,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_106,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_104,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_62,plain,(
    ! [A_31] : v2_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_115,plain,(
    ! [A_31] : v2_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_62])).

tff(c_3465,plain,(
    ! [B_256,F_258,A_255,D_259,C_260,E_257] :
      ( k1_partfun1(A_255,B_256,C_260,D_259,E_257,F_258) = k5_relat_1(E_257,F_258)
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(C_260,D_259)))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ v1_funct_1(E_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3485,plain,(
    ! [A_255,B_256,E_257] :
      ( k1_partfun1(A_255,B_256,'#skF_2','#skF_1',E_257,'#skF_4') = k5_relat_1(E_257,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ v1_funct_1(E_257) ) ),
    inference(resolution,[status(thm)],[c_102,c_3465])).

tff(c_5049,plain,(
    ! [A_312,B_313,E_314] :
      ( k1_partfun1(A_312,B_313,'#skF_2','#skF_1',E_314,'#skF_4') = k5_relat_1(E_314,'#skF_4')
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_1(E_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3485])).

tff(c_5085,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_5049])).

tff(c_5096,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5085])).

tff(c_84,plain,(
    ! [A_50] : m1_subset_1(k6_partfun1(A_50),k1_zfmisc_1(k2_zfmisc_1(A_50,A_50))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_2697,plain,(
    ! [D_217,C_218,A_219,B_220] :
      ( D_217 = C_218
      | ~ r2_relset_1(A_219,B_220,C_218,D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2705,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_100,c_2697])).

tff(c_2720,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2705])).

tff(c_2763,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2720])).

tff(c_6560,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5096,c_2763])).

tff(c_78,plain,(
    ! [C_46,E_48,F_49,A_44,B_45,D_47] :
      ( m1_subset_1(k1_partfun1(A_44,B_45,C_46,D_47,E_48,F_49),k1_zfmisc_1(k2_zfmisc_1(A_44,D_47)))
      | ~ m1_subset_1(F_49,k1_zfmisc_1(k2_zfmisc_1(C_46,D_47)))
      | ~ v1_funct_1(F_49)
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_1(E_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_5345,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5096,c_78])).

tff(c_5352,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_108,c_106,c_102,c_5345])).

tff(c_7607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6560,c_5352])).

tff(c_7608,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2720])).

tff(c_96,plain,(
    ! [D_62,A_59,C_61,B_60,E_64] :
      ( k1_xboole_0 = C_61
      | v2_funct_1(D_62)
      | ~ v2_funct_1(k1_partfun1(A_59,B_60,B_60,C_61,D_62,E_64))
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(B_60,C_61)))
      | ~ v1_funct_2(E_64,B_60,C_61)
      | ~ v1_funct_1(E_64)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(D_62,A_59,B_60)
      | ~ v1_funct_1(D_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_10461,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7608,c_96])).

tff(c_10468,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_108,c_106,c_104,c_102,c_115,c_10461])).

tff(c_10470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_440,c_10468])).

tff(c_10472,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k6_relat_1(A_51))
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_113,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k6_partfun1(A_51))
      | v1_xboole_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88])).

tff(c_354,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(A_101)
      | k1_xboole_0 != A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_113])).

tff(c_379,plain,(
    ! [A_101] :
      ( v1_xboole_0(A_101)
      | k1_xboole_0 != A_101 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_10489,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10472,c_379])).

tff(c_179,plain,(
    ! [A_81,B_82] :
      ( v1_xboole_0(k2_zfmisc_1(A_81,B_82))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_169,plain,(
    ! [B_78,A_79] :
      ( ~ v1_xboole_0(B_78)
      | B_78 = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_172,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_2,c_169])).

tff(c_259,plain,(
    ! [A_96,B_97] :
      ( k2_zfmisc_1(A_96,B_97) = k1_xboole_0
      | ~ v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_179,c_172])).

tff(c_268,plain,(
    ! [B_97] : k2_zfmisc_1(k1_xboole_0,B_97) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_259])).

tff(c_10480,plain,(
    ! [B_97] : k2_zfmisc_1('#skF_1',B_97) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10472,c_10472,c_268])).

tff(c_10567,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_108])).

tff(c_10848,plain,(
    ! [B_518,A_519] :
      ( v1_xboole_0(B_518)
      | ~ m1_subset_1(B_518,k1_zfmisc_1(A_519))
      | ~ v1_xboole_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10857,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10567,c_10848])).

tff(c_10869,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10489,c_10857])).

tff(c_10871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10705,c_10869])).

tff(c_10872,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10704])).

tff(c_10873,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10704])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_relat_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10885,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10873,c_18])).

tff(c_10894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10872,c_10885])).

tff(c_10895,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_11309,plain,(
    ! [C_563,A_564,B_565] :
      ( v1_relat_1(C_563)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_564,B_565))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_11326,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_11309])).

tff(c_12678,plain,(
    ! [C_621,B_622,A_623] :
      ( v5_relat_1(C_621,B_622)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(k2_zfmisc_1(A_623,B_622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_12700,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_12678])).

tff(c_11325,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_11309])).

tff(c_44,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_121,plain,(
    ! [A_27] : k2_relat_1(k6_partfun1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_44])).

tff(c_13329,plain,(
    ! [D_665,C_666,A_667,B_668] :
      ( D_665 = C_666
      | ~ r2_relset_1(A_667,B_668,C_666,D_665)
      | ~ m1_subset_1(D_665,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668)))
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_13337,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_100,c_13329])).

tff(c_13352,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13337])).

tff(c_13398,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_13352])).

tff(c_17151,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_13398])).

tff(c_17167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_108,c_106,c_102,c_17151])).

tff(c_17168,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_13352])).

tff(c_18460,plain,(
    ! [D_835,A_831,E_833,B_832,C_836,F_834] :
      ( k1_partfun1(A_831,B_832,C_836,D_835,E_833,F_834) = k5_relat_1(E_833,F_834)
      | ~ m1_subset_1(F_834,k1_zfmisc_1(k2_zfmisc_1(C_836,D_835)))
      | ~ v1_funct_1(F_834)
      | ~ m1_subset_1(E_833,k1_zfmisc_1(k2_zfmisc_1(A_831,B_832)))
      | ~ v1_funct_1(E_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_18482,plain,(
    ! [A_831,B_832,E_833] :
      ( k1_partfun1(A_831,B_832,'#skF_2','#skF_1',E_833,'#skF_4') = k5_relat_1(E_833,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_833,k1_zfmisc_1(k2_zfmisc_1(A_831,B_832)))
      | ~ v1_funct_1(E_833) ) ),
    inference(resolution,[status(thm)],[c_102,c_18460])).

tff(c_19918,plain,(
    ! [A_888,B_889,E_890] :
      ( k1_partfun1(A_888,B_889,'#skF_2','#skF_1',E_890,'#skF_4') = k5_relat_1(E_890,'#skF_4')
      | ~ m1_subset_1(E_890,k1_zfmisc_1(k2_zfmisc_1(A_888,B_889)))
      | ~ v1_funct_1(E_890) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_18482])).

tff(c_19954,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_19918])).

tff(c_19965,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_17168,c_19954])).

tff(c_36,plain,(
    ! [A_23,B_25] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_23,B_25)),k2_relat_1(B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_19981,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19965,c_36])).

tff(c_20004,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11325,c_11326,c_121,c_19981])).

tff(c_11920,plain,(
    ! [B_593,A_594] :
      ( r1_tarski(k2_relat_1(B_593),A_594)
      | ~ v5_relat_1(B_593,A_594)
      | ~ v1_relat_1(B_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20551,plain,(
    ! [B_909,A_910] :
      ( k2_relat_1(B_909) = A_910
      | ~ r1_tarski(A_910,k2_relat_1(B_909))
      | ~ v5_relat_1(B_909,A_910)
      | ~ v1_relat_1(B_909) ) ),
    inference(resolution,[status(thm)],[c_11920,c_4])).

tff(c_20562,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20004,c_20551])).

tff(c_20603,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11326,c_12700,c_20562])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12581,plain,(
    ! [B_617,A_618] :
      ( v5_relat_1(B_617,A_618)
      | ~ r1_tarski(k2_relat_1(B_617),A_618)
      | ~ v1_relat_1(B_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12595,plain,(
    ! [B_617] :
      ( v5_relat_1(B_617,k2_relat_1(B_617))
      | ~ v1_relat_1(B_617) ) ),
    inference(resolution,[status(thm)],[c_8,c_12581])).

tff(c_12941,plain,(
    ! [B_637] :
      ( v2_funct_2(B_637,k2_relat_1(B_637))
      | ~ v5_relat_1(B_637,k2_relat_1(B_637))
      | ~ v1_relat_1(B_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_12959,plain,(
    ! [B_617] :
      ( v2_funct_2(B_617,k2_relat_1(B_617))
      | ~ v1_relat_1(B_617) ) ),
    inference(resolution,[status(thm)],[c_12595,c_12941])).

tff(c_20636,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20603,c_12959])).

tff(c_20653,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11326,c_20636])).

tff(c_20655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10895,c_20653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.53/4.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/4.40  
% 11.53/4.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.61/4.40  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.61/4.40  
% 11.61/4.40  %Foreground sorts:
% 11.61/4.40  
% 11.61/4.40  
% 11.61/4.40  %Background operators:
% 11.61/4.40  
% 11.61/4.40  
% 11.61/4.40  %Foreground operators:
% 11.61/4.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.61/4.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.61/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.61/4.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.61/4.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.61/4.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.61/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.61/4.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.61/4.40  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.61/4.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.61/4.40  tff('#skF_2', type, '#skF_2': $i).
% 11.61/4.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.61/4.40  tff('#skF_3', type, '#skF_3': $i).
% 11.61/4.40  tff('#skF_1', type, '#skF_1': $i).
% 11.61/4.40  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 11.61/4.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.61/4.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.61/4.40  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.61/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.61/4.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.61/4.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.61/4.40  tff('#skF_4', type, '#skF_4': $i).
% 11.61/4.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.61/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.61/4.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.61/4.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.61/4.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.61/4.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.61/4.40  
% 11.74/4.43  tff(f_243, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 11.74/4.43  tff(f_129, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 11.74/4.43  tff(f_201, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.74/4.43  tff(f_113, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.74/4.43  tff(f_139, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 11.74/4.43  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 11.74/4.43  tff(f_199, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.74/4.43  tff(f_181, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.74/4.43  tff(f_157, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.74/4.43  tff(f_177, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.74/4.43  tff(f_223, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 11.74/4.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.74/4.43  tff(f_189, axiom, (![A]: (~v1_xboole_0(A) => (~v1_xboole_0(k6_relat_1(A)) & v1_relat_1(k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relset_1)).
% 11.74/4.43  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 11.74/4.43  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 11.74/4.43  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.74/4.43  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 11.74/4.43  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.74/4.43  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.74/4.43  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 11.74/4.43  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 11.74/4.43  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.74/4.43  tff(f_165, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 11.74/4.43  tff(c_112, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_10698, plain, (![A_506]: (v2_funct_1(A_506) | ~v1_funct_1(A_506) | ~v1_relat_1(A_506) | ~v1_xboole_0(A_506))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.74/4.43  tff(c_98, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_167, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_98])).
% 11.74/4.43  tff(c_10701, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10698, c_167])).
% 11.74/4.43  tff(c_10704, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_10701])).
% 11.74/4.43  tff(c_10705, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_10704])).
% 11.74/4.43  tff(c_92, plain, (![A_58]: (k6_relat_1(A_58)=k6_partfun1(A_58))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.43  tff(c_42, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.74/4.43  tff(c_122, plain, (![A_27]: (k1_relat_1(k6_partfun1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_42])).
% 11.74/4.43  tff(c_60, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.74/4.43  tff(c_116, plain, (![A_31]: (v1_relat_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_60])).
% 11.74/4.43  tff(c_321, plain, (![A_100]: (k1_relat_1(A_100)!=k1_xboole_0 | k1_xboole_0=A_100 | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.74/4.43  tff(c_333, plain, (![A_31]: (k1_relat_1(k6_partfun1(A_31))!=k1_xboole_0 | k6_partfun1(A_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_116, c_321])).
% 11.74/4.43  tff(c_342, plain, (![A_101]: (k1_xboole_0!=A_101 | k6_partfun1(A_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_333])).
% 11.74/4.43  tff(c_100, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_351, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_342, c_100])).
% 11.74/4.43  tff(c_440, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_351])).
% 11.74/4.43  tff(c_110, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_108, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_106, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_104, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.74/4.43  tff(c_62, plain, (![A_31]: (v2_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.74/4.43  tff(c_115, plain, (![A_31]: (v2_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_62])).
% 11.74/4.43  tff(c_3465, plain, (![B_256, F_258, A_255, D_259, C_260, E_257]: (k1_partfun1(A_255, B_256, C_260, D_259, E_257, F_258)=k5_relat_1(E_257, F_258) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(C_260, D_259))) | ~v1_funct_1(F_258) | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~v1_funct_1(E_257))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.74/4.43  tff(c_3485, plain, (![A_255, B_256, E_257]: (k1_partfun1(A_255, B_256, '#skF_2', '#skF_1', E_257, '#skF_4')=k5_relat_1(E_257, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~v1_funct_1(E_257))), inference(resolution, [status(thm)], [c_102, c_3465])).
% 11.74/4.43  tff(c_5049, plain, (![A_312, B_313, E_314]: (k1_partfun1(A_312, B_313, '#skF_2', '#skF_1', E_314, '#skF_4')=k5_relat_1(E_314, '#skF_4') | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | ~v1_funct_1(E_314))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3485])).
% 11.74/4.43  tff(c_5085, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_5049])).
% 11.74/4.43  tff(c_5096, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_5085])).
% 11.74/4.43  tff(c_84, plain, (![A_50]: (m1_subset_1(k6_partfun1(A_50), k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/4.43  tff(c_2697, plain, (![D_217, C_218, A_219, B_220]: (D_217=C_218 | ~r2_relset_1(A_219, B_220, C_218, D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.74/4.43  tff(c_2705, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_100, c_2697])).
% 11.74/4.43  tff(c_2720, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2705])).
% 11.74/4.43  tff(c_2763, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2720])).
% 11.74/4.43  tff(c_6560, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5096, c_2763])).
% 11.74/4.43  tff(c_78, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (m1_subset_1(k1_partfun1(A_44, B_45, C_46, D_47, E_48, F_49), k1_zfmisc_1(k2_zfmisc_1(A_44, D_47))) | ~m1_subset_1(F_49, k1_zfmisc_1(k2_zfmisc_1(C_46, D_47))) | ~v1_funct_1(F_49) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_1(E_48))), inference(cnfTransformation, [status(thm)], [f_177])).
% 11.74/4.43  tff(c_5345, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5096, c_78])).
% 11.74/4.43  tff(c_5352, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_108, c_106, c_102, c_5345])).
% 11.74/4.43  tff(c_7607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6560, c_5352])).
% 11.74/4.43  tff(c_7608, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2720])).
% 11.74/4.43  tff(c_96, plain, (![D_62, A_59, C_61, B_60, E_64]: (k1_xboole_0=C_61 | v2_funct_1(D_62) | ~v2_funct_1(k1_partfun1(A_59, B_60, B_60, C_61, D_62, E_64)) | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(B_60, C_61))) | ~v1_funct_2(E_64, B_60, C_61) | ~v1_funct_1(E_64) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(D_62, A_59, B_60) | ~v1_funct_1(D_62))), inference(cnfTransformation, [status(thm)], [f_223])).
% 11.74/4.43  tff(c_10461, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7608, c_96])).
% 11.74/4.43  tff(c_10468, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_108, c_106, c_104, c_102, c_115, c_10461])).
% 11.74/4.43  tff(c_10470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_440, c_10468])).
% 11.74/4.43  tff(c_10472, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_351])).
% 11.74/4.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.74/4.43  tff(c_88, plain, (![A_51]: (~v1_xboole_0(k6_relat_1(A_51)) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.74/4.43  tff(c_113, plain, (![A_51]: (~v1_xboole_0(k6_partfun1(A_51)) | v1_xboole_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88])).
% 11.74/4.43  tff(c_354, plain, (![A_101]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(A_101) | k1_xboole_0!=A_101)), inference(superposition, [status(thm), theory('equality')], [c_342, c_113])).
% 11.74/4.43  tff(c_379, plain, (![A_101]: (v1_xboole_0(A_101) | k1_xboole_0!=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_354])).
% 11.74/4.43  tff(c_10489, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10472, c_379])).
% 11.74/4.43  tff(c_179, plain, (![A_81, B_82]: (v1_xboole_0(k2_zfmisc_1(A_81, B_82)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.74/4.43  tff(c_169, plain, (![B_78, A_79]: (~v1_xboole_0(B_78) | B_78=A_79 | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.74/4.43  tff(c_172, plain, (![A_79]: (k1_xboole_0=A_79 | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_2, c_169])).
% 11.74/4.43  tff(c_259, plain, (![A_96, B_97]: (k2_zfmisc_1(A_96, B_97)=k1_xboole_0 | ~v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_179, c_172])).
% 11.74/4.43  tff(c_268, plain, (![B_97]: (k2_zfmisc_1(k1_xboole_0, B_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_259])).
% 11.74/4.43  tff(c_10480, plain, (![B_97]: (k2_zfmisc_1('#skF_1', B_97)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10472, c_10472, c_268])).
% 11.74/4.43  tff(c_10567, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_108])).
% 11.74/4.43  tff(c_10848, plain, (![B_518, A_519]: (v1_xboole_0(B_518) | ~m1_subset_1(B_518, k1_zfmisc_1(A_519)) | ~v1_xboole_0(A_519))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.74/4.43  tff(c_10857, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10567, c_10848])).
% 11.74/4.43  tff(c_10869, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10489, c_10857])).
% 11.74/4.43  tff(c_10871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10705, c_10869])).
% 11.74/4.43  tff(c_10872, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_10704])).
% 11.74/4.43  tff(c_10873, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_10704])).
% 11.74/4.43  tff(c_18, plain, (![A_12]: (v1_relat_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.74/4.43  tff(c_10885, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10873, c_18])).
% 11.74/4.43  tff(c_10894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10872, c_10885])).
% 11.74/4.43  tff(c_10895, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_98])).
% 11.74/4.43  tff(c_11309, plain, (![C_563, A_564, B_565]: (v1_relat_1(C_563) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_564, B_565))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.74/4.43  tff(c_11326, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_11309])).
% 11.74/4.43  tff(c_12678, plain, (![C_621, B_622, A_623]: (v5_relat_1(C_621, B_622) | ~m1_subset_1(C_621, k1_zfmisc_1(k2_zfmisc_1(A_623, B_622))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.74/4.43  tff(c_12700, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_102, c_12678])).
% 11.74/4.43  tff(c_11325, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_11309])).
% 11.74/4.43  tff(c_44, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.74/4.43  tff(c_121, plain, (![A_27]: (k2_relat_1(k6_partfun1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_44])).
% 11.74/4.43  tff(c_13329, plain, (![D_665, C_666, A_667, B_668]: (D_665=C_666 | ~r2_relset_1(A_667, B_668, C_666, D_665) | ~m1_subset_1(D_665, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.74/4.43  tff(c_13337, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_100, c_13329])).
% 11.74/4.43  tff(c_13352, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_13337])).
% 11.74/4.43  tff(c_13398, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_13352])).
% 11.74/4.43  tff(c_17151, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_13398])).
% 11.74/4.43  tff(c_17167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_108, c_106, c_102, c_17151])).
% 11.74/4.43  tff(c_17168, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_13352])).
% 11.74/4.43  tff(c_18460, plain, (![D_835, A_831, E_833, B_832, C_836, F_834]: (k1_partfun1(A_831, B_832, C_836, D_835, E_833, F_834)=k5_relat_1(E_833, F_834) | ~m1_subset_1(F_834, k1_zfmisc_1(k2_zfmisc_1(C_836, D_835))) | ~v1_funct_1(F_834) | ~m1_subset_1(E_833, k1_zfmisc_1(k2_zfmisc_1(A_831, B_832))) | ~v1_funct_1(E_833))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.74/4.43  tff(c_18482, plain, (![A_831, B_832, E_833]: (k1_partfun1(A_831, B_832, '#skF_2', '#skF_1', E_833, '#skF_4')=k5_relat_1(E_833, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_833, k1_zfmisc_1(k2_zfmisc_1(A_831, B_832))) | ~v1_funct_1(E_833))), inference(resolution, [status(thm)], [c_102, c_18460])).
% 11.74/4.43  tff(c_19918, plain, (![A_888, B_889, E_890]: (k1_partfun1(A_888, B_889, '#skF_2', '#skF_1', E_890, '#skF_4')=k5_relat_1(E_890, '#skF_4') | ~m1_subset_1(E_890, k1_zfmisc_1(k2_zfmisc_1(A_888, B_889))) | ~v1_funct_1(E_890))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_18482])).
% 11.74/4.43  tff(c_19954, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_19918])).
% 11.74/4.43  tff(c_19965, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_17168, c_19954])).
% 11.74/4.43  tff(c_36, plain, (![A_23, B_25]: (r1_tarski(k2_relat_1(k5_relat_1(A_23, B_25)), k2_relat_1(B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.74/4.43  tff(c_19981, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19965, c_36])).
% 11.74/4.43  tff(c_20004, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11325, c_11326, c_121, c_19981])).
% 11.74/4.43  tff(c_11920, plain, (![B_593, A_594]: (r1_tarski(k2_relat_1(B_593), A_594) | ~v5_relat_1(B_593, A_594) | ~v1_relat_1(B_593))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.74/4.43  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.74/4.43  tff(c_20551, plain, (![B_909, A_910]: (k2_relat_1(B_909)=A_910 | ~r1_tarski(A_910, k2_relat_1(B_909)) | ~v5_relat_1(B_909, A_910) | ~v1_relat_1(B_909))), inference(resolution, [status(thm)], [c_11920, c_4])).
% 11.74/4.43  tff(c_20562, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20004, c_20551])).
% 11.74/4.43  tff(c_20603, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11326, c_12700, c_20562])).
% 11.74/4.43  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.74/4.43  tff(c_12581, plain, (![B_617, A_618]: (v5_relat_1(B_617, A_618) | ~r1_tarski(k2_relat_1(B_617), A_618) | ~v1_relat_1(B_617))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.74/4.43  tff(c_12595, plain, (![B_617]: (v5_relat_1(B_617, k2_relat_1(B_617)) | ~v1_relat_1(B_617))), inference(resolution, [status(thm)], [c_8, c_12581])).
% 11.74/4.43  tff(c_12941, plain, (![B_637]: (v2_funct_2(B_637, k2_relat_1(B_637)) | ~v5_relat_1(B_637, k2_relat_1(B_637)) | ~v1_relat_1(B_637))), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.74/4.43  tff(c_12959, plain, (![B_617]: (v2_funct_2(B_617, k2_relat_1(B_617)) | ~v1_relat_1(B_617))), inference(resolution, [status(thm)], [c_12595, c_12941])).
% 11.74/4.43  tff(c_20636, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20603, c_12959])).
% 11.74/4.43  tff(c_20653, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11326, c_20636])).
% 11.74/4.43  tff(c_20655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10895, c_20653])).
% 11.74/4.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/4.43  
% 11.74/4.43  Inference rules
% 11.74/4.43  ----------------------
% 11.74/4.43  #Ref     : 22
% 11.74/4.43  #Sup     : 4948
% 11.74/4.43  #Fact    : 0
% 11.74/4.43  #Define  : 0
% 11.74/4.43  #Split   : 44
% 11.74/4.43  #Chain   : 0
% 11.74/4.43  #Close   : 0
% 11.74/4.43  
% 11.74/4.43  Ordering : KBO
% 11.74/4.43  
% 11.74/4.43  Simplification rules
% 11.74/4.43  ----------------------
% 11.74/4.43  #Subsume      : 1736
% 11.74/4.43  #Demod        : 3313
% 11.74/4.43  #Tautology    : 2537
% 11.74/4.43  #SimpNegUnit  : 323
% 11.74/4.43  #BackRed      : 134
% 11.74/4.43  
% 11.74/4.43  #Partial instantiations: 0
% 11.74/4.43  #Strategies tried      : 1
% 11.74/4.43  
% 11.74/4.43  Timing (in seconds)
% 11.74/4.43  ----------------------
% 11.74/4.43  Preprocessing        : 0.39
% 11.74/4.43  Parsing              : 0.21
% 11.74/4.43  CNF conversion       : 0.03
% 11.74/4.44  Main loop            : 3.27
% 11.74/4.44  Inferencing          : 0.83
% 11.74/4.44  Reduction            : 1.23
% 11.74/4.44  Demodulation         : 0.89
% 11.74/4.44  BG Simplification    : 0.09
% 11.74/4.44  Subsumption          : 0.90
% 11.74/4.44  Abstraction          : 0.11
% 11.74/4.44  MUC search           : 0.00
% 11.74/4.44  Cooper               : 0.00
% 11.74/4.44  Total                : 3.72
% 11.74/4.44  Index Insertion      : 0.00
% 11.74/4.44  Index Deletion       : 0.00
% 11.74/4.44  Index Matching       : 0.00
% 11.74/4.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
