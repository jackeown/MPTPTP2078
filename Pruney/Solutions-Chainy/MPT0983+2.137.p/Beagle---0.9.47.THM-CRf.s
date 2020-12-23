%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:21 EST 2020

% Result     : Theorem 12.68s
% Output     : CNFRefutation 12.80s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 439 expanded)
%              Number of leaves         :   56 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  300 (1208 expanded)
%              Number of equality atoms :   55 ( 135 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
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

tff(f_127,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_169,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_167,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_191,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_100,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_529,plain,(
    ! [C_141,B_142,A_143] :
      ( v1_xboole_0(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(B_142,A_143)))
      | ~ v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_551,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_529])).

tff(c_555,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_96,plain,
    ( ~ v2_funct_2('#skF_8','#skF_5')
    | ~ v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_184,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_110,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_108,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_106,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_104,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_102,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_90,plain,(
    ! [A_66] : k6_relat_1(A_66) = k6_partfun1(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_64,plain,(
    ! [A_35] : v2_funct_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_112,plain,(
    ! [A_35] : v2_funct_1(k6_partfun1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64])).

tff(c_1788,plain,(
    ! [F_236,A_239,B_238,D_237,C_235,E_240] :
      ( k1_partfun1(A_239,B_238,C_235,D_237,E_240,F_236) = k5_relat_1(E_240,F_236)
      | ~ m1_subset_1(F_236,k1_zfmisc_1(k2_zfmisc_1(C_235,D_237)))
      | ~ v1_funct_1(F_236)
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238)))
      | ~ v1_funct_1(E_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1795,plain,(
    ! [A_239,B_238,E_240] :
      ( k1_partfun1(A_239,B_238,'#skF_6','#skF_5',E_240,'#skF_8') = k5_relat_1(E_240,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238)))
      | ~ v1_funct_1(E_240) ) ),
    inference(resolution,[status(thm)],[c_100,c_1788])).

tff(c_2365,plain,(
    ! [A_285,B_286,E_287] :
      ( k1_partfun1(A_285,B_286,'#skF_6','#skF_5',E_287,'#skF_8') = k5_relat_1(E_287,'#skF_8')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1795])).

tff(c_2381,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k5_relat_1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_106,c_2365])).

tff(c_2396,plain,(
    k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k5_relat_1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2381])).

tff(c_84,plain,(
    ! [C_56,E_58,F_59,D_57,B_55,A_54] :
      ( m1_subset_1(k1_partfun1(A_54,B_55,C_56,D_57,E_58,F_59),k1_zfmisc_1(k2_zfmisc_1(A_54,D_57)))
      | ~ m1_subset_1(F_59,k1_zfmisc_1(k2_zfmisc_1(C_56,D_57)))
      | ~ v1_funct_1(F_59)
      | ~ m1_subset_1(E_58,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_1(E_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2907,plain,
    ( m1_subset_1(k5_relat_1('#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2396,c_84])).

tff(c_2914,plain,(
    m1_subset_1(k5_relat_1('#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_104,c_100,c_2907])).

tff(c_78,plain,(
    ! [A_51] : m1_subset_1(k6_relat_1(A_51),k1_zfmisc_1(k2_zfmisc_1(A_51,A_51))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_111,plain,(
    ! [A_51] : m1_subset_1(k6_partfun1(A_51),k1_zfmisc_1(k2_zfmisc_1(A_51,A_51))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_78])).

tff(c_98,plain,(
    r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k6_partfun1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_1423,plain,(
    ! [D_200,C_201,A_202,B_203] :
      ( D_200 = C_201
      | ~ r2_relset_1(A_202,B_203,C_201,D_200)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1433,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_98,c_1423])).

tff(c_1452,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1433])).

tff(c_1540,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1452])).

tff(c_3524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2914,c_2396,c_1540])).

tff(c_3525,plain,(
    k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1452])).

tff(c_94,plain,(
    ! [E_72,D_70,B_68,A_67,C_69] :
      ( k1_xboole_0 = C_69
      | v2_funct_1(D_70)
      | ~ v2_funct_1(k1_partfun1(A_67,B_68,B_68,C_69,D_70,E_72))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(B_68,C_69)))
      | ~ v1_funct_2(E_72,B_68,C_69)
      | ~ v1_funct_1(E_72)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(D_70,A_67,B_68)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4797,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_funct_1('#skF_7')
    | ~ v2_funct_1(k6_partfun1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3525,c_94])).

tff(c_4804,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_106,c_104,c_102,c_100,c_112,c_4797])).

tff(c_4805,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_4804])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4862,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4805,c_2])).

tff(c_4864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_4862])).

tff(c_4865,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4874,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4865,c_4])).

tff(c_28,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_185,plain,(
    ! [A_86,B_87] : ~ r2_hidden(A_86,k2_zfmisc_1(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_188,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_185])).

tff(c_4896,plain,(
    ! [A_10] : ~ r2_hidden(A_10,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_188])).

tff(c_44,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_272,plain,(
    ! [B_103,A_104] :
      ( v1_relat_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_284,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_100,c_272])).

tff(c_297,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_284])).

tff(c_193,plain,(
    ! [A_89] :
      ( v1_xboole_0(k1_relat_1(A_89))
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_200,plain,(
    ! [A_89] :
      ( k1_relat_1(A_89) = k1_xboole_0
      | ~ v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_193,c_4])).

tff(c_4873,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4865,c_200])).

tff(c_4923,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_4873])).

tff(c_5088,plain,(
    ! [A_422] :
      ( r2_hidden('#skF_3'(A_422),k1_relat_1(A_422))
      | v2_funct_1(A_422)
      | ~ v1_funct_1(A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5094,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4923,c_5088])).

tff(c_5100,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | v2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_104,c_5094])).

tff(c_5101,plain,(
    v2_funct_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_4896,c_5100])).

tff(c_30,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4899,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_8',B_11) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_4874,c_30])).

tff(c_4866,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_4882,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4866,c_4])).

tff(c_4909,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_4882])).

tff(c_4915,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_106])).

tff(c_5128,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_4915])).

tff(c_545,plain,(
    ! [C_141] :
      ( v1_xboole_0(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_529])).

tff(c_554,plain,(
    ! [C_141] :
      ( v1_xboole_0(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_545])).

tff(c_5278,plain,(
    ! [C_432] :
      ( v1_xboole_0(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_554])).

tff(c_5289,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_5128,c_5278])).

tff(c_4900,plain,(
    ! [A_1] :
      ( A_1 = '#skF_8'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_4])).

tff(c_5304,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5289,c_4900])).

tff(c_5313,plain,(
    ~ v2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5304,c_184])).

tff(c_5322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5101,c_5313])).

tff(c_5323,plain,(
    ~ v2_funct_2('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_5435,plain,(
    ! [B_453,A_454] :
      ( v1_relat_1(B_453)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(A_454))
      | ~ v1_relat_1(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5450,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_100,c_5435])).

tff(c_5463,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5450])).

tff(c_5531,plain,(
    ! [C_468,B_469,A_470] :
      ( v5_relat_1(C_468,B_469)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_470,B_469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5554,plain,(
    v5_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_5531])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5447,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_106,c_5435])).

tff(c_5460,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5447])).

tff(c_50,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_114,plain,(
    ! [A_27] : k2_relat_1(k6_partfun1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_50])).

tff(c_7405,plain,(
    ! [E_615,B_619,A_617,F_618,C_616,D_620] :
      ( m1_subset_1(k1_partfun1(A_617,B_619,C_616,D_620,E_615,F_618),k1_zfmisc_1(k2_zfmisc_1(A_617,D_620)))
      | ~ m1_subset_1(F_618,k1_zfmisc_1(k2_zfmisc_1(C_616,D_620)))
      | ~ v1_funct_1(F_618)
      | ~ m1_subset_1(E_615,k1_zfmisc_1(k2_zfmisc_1(A_617,B_619)))
      | ~ v1_funct_1(E_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6691,plain,(
    ! [D_554,C_555,A_556,B_557] :
      ( D_554 = C_555
      | ~ r2_relset_1(A_556,B_557,C_555,D_554)
      | ~ m1_subset_1(D_554,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557)))
      | ~ m1_subset_1(C_555,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6701,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_98,c_6691])).

tff(c_6720,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_6701])).

tff(c_6725,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_6720])).

tff(c_7418,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7405,c_6725])).

tff(c_7449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_104,c_100,c_7418])).

tff(c_7450,plain,(
    k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6720])).

tff(c_8035,plain,(
    ! [B_670,E_672,C_667,A_671,D_669,F_668] :
      ( k1_partfun1(A_671,B_670,C_667,D_669,E_672,F_668) = k5_relat_1(E_672,F_668)
      | ~ m1_subset_1(F_668,k1_zfmisc_1(k2_zfmisc_1(C_667,D_669)))
      | ~ v1_funct_1(F_668)
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(A_671,B_670)))
      | ~ v1_funct_1(E_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_8044,plain,(
    ! [A_671,B_670,E_672] :
      ( k1_partfun1(A_671,B_670,'#skF_6','#skF_5',E_672,'#skF_8') = k5_relat_1(E_672,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(A_671,B_670)))
      | ~ v1_funct_1(E_672) ) ),
    inference(resolution,[status(thm)],[c_100,c_8035])).

tff(c_8897,plain,(
    ! [A_717,B_718,E_719] :
      ( k1_partfun1(A_717,B_718,'#skF_6','#skF_5',E_719,'#skF_8') = k5_relat_1(E_719,'#skF_8')
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(A_717,B_718)))
      | ~ v1_funct_1(E_719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_8044])).

tff(c_8916,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k5_relat_1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_106,c_8897])).

tff(c_8937,plain,(
    k5_relat_1('#skF_7','#skF_8') = k6_partfun1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_7450,c_8916])).

tff(c_46,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_24,B_26)),k2_relat_1(B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8944,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_5')),k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8937,c_46])).

tff(c_8948,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5460,c_5463,c_114,c_8944])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8960,plain,
    ( k2_relat_1('#skF_8') = '#skF_5'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8948,c_6])).

tff(c_9064,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8960])).

tff(c_9070,plain,
    ( ~ v5_relat_1('#skF_8','#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_9064])).

tff(c_9075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5463,c_5554,c_9070])).

tff(c_9076,plain,(
    k2_relat_1('#skF_8') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8960])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5585,plain,(
    ! [B_481,A_482] :
      ( v5_relat_1(B_481,A_482)
      | ~ r1_tarski(k2_relat_1(B_481),A_482)
      | ~ v1_relat_1(B_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5599,plain,(
    ! [B_481] :
      ( v5_relat_1(B_481,k2_relat_1(B_481))
      | ~ v1_relat_1(B_481) ) ),
    inference(resolution,[status(thm)],[c_10,c_5585])).

tff(c_5634,plain,(
    ! [B_488] :
      ( v2_funct_2(B_488,k2_relat_1(B_488))
      | ~ v5_relat_1(B_488,k2_relat_1(B_488))
      | ~ v1_relat_1(B_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5656,plain,(
    ! [B_481] :
      ( v2_funct_2(B_481,k2_relat_1(B_481))
      | ~ v1_relat_1(B_481) ) ),
    inference(resolution,[status(thm)],[c_5599,c_5634])).

tff(c_9096,plain,
    ( v2_funct_2('#skF_8','#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_9076,c_5656])).

tff(c_9118,plain,(
    v2_funct_2('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5463,c_9096])).

tff(c_9120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5323,c_9118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.68/4.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.68/4.26  
% 12.68/4.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.68/4.27  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 12.68/4.27  
% 12.68/4.27  %Foreground sorts:
% 12.68/4.27  
% 12.68/4.27  
% 12.68/4.27  %Background operators:
% 12.68/4.27  
% 12.68/4.27  
% 12.68/4.27  %Foreground operators:
% 12.68/4.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.68/4.27  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.68/4.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.68/4.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.68/4.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.68/4.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.68/4.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.68/4.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.68/4.27  tff('#skF_7', type, '#skF_7': $i).
% 12.68/4.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.68/4.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.68/4.27  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.68/4.27  tff('#skF_5', type, '#skF_5': $i).
% 12.68/4.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.68/4.27  tff('#skF_6', type, '#skF_6': $i).
% 12.68/4.27  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 12.68/4.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.68/4.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.68/4.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.68/4.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.68/4.27  tff('#skF_8', type, '#skF_8': $i).
% 12.68/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.68/4.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.68/4.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.68/4.27  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.68/4.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.68/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.68/4.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.68/4.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.68/4.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.68/4.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.68/4.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.68/4.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.68/4.27  
% 12.80/4.31  tff(f_211, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 12.80/4.31  tff(f_127, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.80/4.31  tff(f_169, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.80/4.31  tff(f_107, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 12.80/4.31  tff(f_167, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.80/4.31  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.80/4.31  tff(f_137, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 12.80/4.31  tff(f_135, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.80/4.31  tff(f_191, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 12.80/4.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.80/4.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.80/4.31  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.80/4.31  tff(f_54, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 12.80/4.31  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.80/4.31  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.80/4.31  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 12.80/4.31  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 12.80/4.31  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.80/4.31  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 12.80/4.31  tff(f_88, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 12.80/4.31  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 12.80/4.31  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.80/4.31  tff(f_145, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 12.80/4.31  tff(c_100, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_529, plain, (![C_141, B_142, A_143]: (v1_xboole_0(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(B_142, A_143))) | ~v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.80/4.31  tff(c_551, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_100, c_529])).
% 12.80/4.31  tff(c_555, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_551])).
% 12.80/4.31  tff(c_96, plain, (~v2_funct_2('#skF_8', '#skF_5') | ~v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_184, plain, (~v2_funct_1('#skF_7')), inference(splitLeft, [status(thm)], [c_96])).
% 12.80/4.31  tff(c_110, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_108, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_106, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_104, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_102, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_90, plain, (![A_66]: (k6_relat_1(A_66)=k6_partfun1(A_66))), inference(cnfTransformation, [status(thm)], [f_169])).
% 12.80/4.31  tff(c_64, plain, (![A_35]: (v2_funct_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.80/4.31  tff(c_112, plain, (![A_35]: (v2_funct_1(k6_partfun1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64])).
% 12.80/4.31  tff(c_1788, plain, (![F_236, A_239, B_238, D_237, C_235, E_240]: (k1_partfun1(A_239, B_238, C_235, D_237, E_240, F_236)=k5_relat_1(E_240, F_236) | ~m1_subset_1(F_236, k1_zfmisc_1(k2_zfmisc_1(C_235, D_237))) | ~v1_funct_1(F_236) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))) | ~v1_funct_1(E_240))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.80/4.31  tff(c_1795, plain, (![A_239, B_238, E_240]: (k1_partfun1(A_239, B_238, '#skF_6', '#skF_5', E_240, '#skF_8')=k5_relat_1(E_240, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))) | ~v1_funct_1(E_240))), inference(resolution, [status(thm)], [c_100, c_1788])).
% 12.80/4.31  tff(c_2365, plain, (![A_285, B_286, E_287]: (k1_partfun1(A_285, B_286, '#skF_6', '#skF_5', E_287, '#skF_8')=k5_relat_1(E_287, '#skF_8') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1795])).
% 12.80/4.31  tff(c_2381, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k5_relat_1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_106, c_2365])).
% 12.80/4.31  tff(c_2396, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k5_relat_1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2381])).
% 12.80/4.31  tff(c_84, plain, (![C_56, E_58, F_59, D_57, B_55, A_54]: (m1_subset_1(k1_partfun1(A_54, B_55, C_56, D_57, E_58, F_59), k1_zfmisc_1(k2_zfmisc_1(A_54, D_57))) | ~m1_subset_1(F_59, k1_zfmisc_1(k2_zfmisc_1(C_56, D_57))) | ~v1_funct_1(F_59) | ~m1_subset_1(E_58, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_1(E_58))), inference(cnfTransformation, [status(thm)], [f_157])).
% 12.80/4.31  tff(c_2907, plain, (m1_subset_1(k5_relat_1('#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2396, c_84])).
% 12.80/4.31  tff(c_2914, plain, (m1_subset_1(k5_relat_1('#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_104, c_100, c_2907])).
% 12.80/4.31  tff(c_78, plain, (![A_51]: (m1_subset_1(k6_relat_1(A_51), k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.80/4.31  tff(c_111, plain, (![A_51]: (m1_subset_1(k6_partfun1(A_51), k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_78])).
% 12.80/4.31  tff(c_98, plain, (r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k6_partfun1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 12.80/4.31  tff(c_1423, plain, (![D_200, C_201, A_202, B_203]: (D_200=C_201 | ~r2_relset_1(A_202, B_203, C_201, D_200) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.80/4.31  tff(c_1433, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_98, c_1423])).
% 12.80/4.31  tff(c_1452, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1433])).
% 12.80/4.31  tff(c_1540, plain, (~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1452])).
% 12.80/4.31  tff(c_3524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2914, c_2396, c_1540])).
% 12.80/4.31  tff(c_3525, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_1452])).
% 12.80/4.31  tff(c_94, plain, (![E_72, D_70, B_68, A_67, C_69]: (k1_xboole_0=C_69 | v2_funct_1(D_70) | ~v2_funct_1(k1_partfun1(A_67, B_68, B_68, C_69, D_70, E_72)) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(B_68, C_69))) | ~v1_funct_2(E_72, B_68, C_69) | ~v1_funct_1(E_72) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(D_70, A_67, B_68) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_191])).
% 12.80/4.31  tff(c_4797, plain, (k1_xboole_0='#skF_5' | v2_funct_1('#skF_7') | ~v2_funct_1(k6_partfun1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3525, c_94])).
% 12.80/4.31  tff(c_4804, plain, (k1_xboole_0='#skF_5' | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_106, c_104, c_102, c_100, c_112, c_4797])).
% 12.80/4.31  tff(c_4805, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_184, c_4804])).
% 12.80/4.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.80/4.31  tff(c_4862, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4805, c_2])).
% 12.80/4.31  tff(c_4864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_4862])).
% 12.80/4.31  tff(c_4865, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_551])).
% 12.80/4.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.80/4.31  tff(c_4874, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_4865, c_4])).
% 12.80/4.31  tff(c_28, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.80/4.31  tff(c_185, plain, (![A_86, B_87]: (~r2_hidden(A_86, k2_zfmisc_1(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.80/4.31  tff(c_188, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_185])).
% 12.80/4.31  tff(c_4896, plain, (![A_10]: (~r2_hidden(A_10, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4874, c_188])).
% 12.80/4.31  tff(c_44, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.80/4.31  tff(c_272, plain, (![B_103, A_104]: (v1_relat_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.80/4.31  tff(c_284, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_272])).
% 12.80/4.31  tff(c_297, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_284])).
% 12.80/4.31  tff(c_193, plain, (![A_89]: (v1_xboole_0(k1_relat_1(A_89)) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.80/4.31  tff(c_200, plain, (![A_89]: (k1_relat_1(A_89)=k1_xboole_0 | ~v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_193, c_4])).
% 12.80/4.31  tff(c_4873, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_4865, c_200])).
% 12.80/4.31  tff(c_4923, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4874, c_4873])).
% 12.80/4.31  tff(c_5088, plain, (![A_422]: (r2_hidden('#skF_3'(A_422), k1_relat_1(A_422)) | v2_funct_1(A_422) | ~v1_funct_1(A_422) | ~v1_relat_1(A_422))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.80/4.31  tff(c_5094, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4923, c_5088])).
% 12.80/4.31  tff(c_5100, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | v2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_104, c_5094])).
% 12.80/4.31  tff(c_5101, plain, (v2_funct_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4896, c_5100])).
% 12.80/4.31  tff(c_30, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.80/4.31  tff(c_4899, plain, (![B_11]: (k2_zfmisc_1('#skF_8', B_11)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4874, c_4874, c_30])).
% 12.80/4.31  tff(c_4866, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_551])).
% 12.80/4.31  tff(c_4882, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4866, c_4])).
% 12.80/4.31  tff(c_4909, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4874, c_4882])).
% 12.80/4.31  tff(c_4915, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_106])).
% 12.80/4.31  tff(c_5128, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_4915])).
% 12.80/4.31  tff(c_545, plain, (![C_141]: (v1_xboole_0(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_529])).
% 12.80/4.31  tff(c_554, plain, (![C_141]: (v1_xboole_0(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_545])).
% 12.80/4.31  tff(c_5278, plain, (![C_432]: (v1_xboole_0(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_4874, c_554])).
% 12.80/4.31  tff(c_5289, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_5128, c_5278])).
% 12.80/4.31  tff(c_4900, plain, (![A_1]: (A_1='#skF_8' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4874, c_4])).
% 12.80/4.31  tff(c_5304, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_5289, c_4900])).
% 12.80/4.31  tff(c_5313, plain, (~v2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5304, c_184])).
% 12.80/4.31  tff(c_5322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5101, c_5313])).
% 12.80/4.31  tff(c_5323, plain, (~v2_funct_2('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_96])).
% 12.80/4.31  tff(c_5435, plain, (![B_453, A_454]: (v1_relat_1(B_453) | ~m1_subset_1(B_453, k1_zfmisc_1(A_454)) | ~v1_relat_1(A_454))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.80/4.31  tff(c_5450, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_5435])).
% 12.80/4.31  tff(c_5463, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5450])).
% 12.80/4.31  tff(c_5531, plain, (![C_468, B_469, A_470]: (v5_relat_1(C_468, B_469) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_470, B_469))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.80/4.31  tff(c_5554, plain, (v5_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_100, c_5531])).
% 12.80/4.31  tff(c_40, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.80/4.31  tff(c_5447, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_106, c_5435])).
% 12.80/4.31  tff(c_5460, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5447])).
% 12.80/4.31  tff(c_50, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.80/4.31  tff(c_114, plain, (![A_27]: (k2_relat_1(k6_partfun1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_50])).
% 12.80/4.31  tff(c_7405, plain, (![E_615, B_619, A_617, F_618, C_616, D_620]: (m1_subset_1(k1_partfun1(A_617, B_619, C_616, D_620, E_615, F_618), k1_zfmisc_1(k2_zfmisc_1(A_617, D_620))) | ~m1_subset_1(F_618, k1_zfmisc_1(k2_zfmisc_1(C_616, D_620))) | ~v1_funct_1(F_618) | ~m1_subset_1(E_615, k1_zfmisc_1(k2_zfmisc_1(A_617, B_619))) | ~v1_funct_1(E_615))), inference(cnfTransformation, [status(thm)], [f_157])).
% 12.80/4.31  tff(c_6691, plain, (![D_554, C_555, A_556, B_557]: (D_554=C_555 | ~r2_relset_1(A_556, B_557, C_555, D_554) | ~m1_subset_1(D_554, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))) | ~m1_subset_1(C_555, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.80/4.31  tff(c_6701, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_98, c_6691])).
% 12.80/4.31  tff(c_6720, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_6701])).
% 12.80/4.31  tff(c_6725, plain, (~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(splitLeft, [status(thm)], [c_6720])).
% 12.80/4.31  tff(c_7418, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_7405, c_6725])).
% 12.80/4.31  tff(c_7449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_104, c_100, c_7418])).
% 12.80/4.31  tff(c_7450, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_6720])).
% 12.80/4.31  tff(c_8035, plain, (![B_670, E_672, C_667, A_671, D_669, F_668]: (k1_partfun1(A_671, B_670, C_667, D_669, E_672, F_668)=k5_relat_1(E_672, F_668) | ~m1_subset_1(F_668, k1_zfmisc_1(k2_zfmisc_1(C_667, D_669))) | ~v1_funct_1(F_668) | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(A_671, B_670))) | ~v1_funct_1(E_672))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.80/4.31  tff(c_8044, plain, (![A_671, B_670, E_672]: (k1_partfun1(A_671, B_670, '#skF_6', '#skF_5', E_672, '#skF_8')=k5_relat_1(E_672, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(A_671, B_670))) | ~v1_funct_1(E_672))), inference(resolution, [status(thm)], [c_100, c_8035])).
% 12.80/4.31  tff(c_8897, plain, (![A_717, B_718, E_719]: (k1_partfun1(A_717, B_718, '#skF_6', '#skF_5', E_719, '#skF_8')=k5_relat_1(E_719, '#skF_8') | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(A_717, B_718))) | ~v1_funct_1(E_719))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_8044])).
% 12.80/4.31  tff(c_8916, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k5_relat_1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_106, c_8897])).
% 12.80/4.31  tff(c_8937, plain, (k5_relat_1('#skF_7', '#skF_8')=k6_partfun1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_7450, c_8916])).
% 12.80/4.31  tff(c_46, plain, (![A_24, B_26]: (r1_tarski(k2_relat_1(k5_relat_1(A_24, B_26)), k2_relat_1(B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.80/4.31  tff(c_8944, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_5')), k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8937, c_46])).
% 12.80/4.31  tff(c_8948, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5460, c_5463, c_114, c_8944])).
% 12.80/4.31  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.80/4.31  tff(c_8960, plain, (k2_relat_1('#skF_8')='#skF_5' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_8948, c_6])).
% 12.80/4.31  tff(c_9064, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_8960])).
% 12.80/4.31  tff(c_9070, plain, (~v5_relat_1('#skF_8', '#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_9064])).
% 12.80/4.31  tff(c_9075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5463, c_5554, c_9070])).
% 12.80/4.31  tff(c_9076, plain, (k2_relat_1('#skF_8')='#skF_5'), inference(splitRight, [status(thm)], [c_8960])).
% 12.80/4.31  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.80/4.31  tff(c_5585, plain, (![B_481, A_482]: (v5_relat_1(B_481, A_482) | ~r1_tarski(k2_relat_1(B_481), A_482) | ~v1_relat_1(B_481))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.80/4.31  tff(c_5599, plain, (![B_481]: (v5_relat_1(B_481, k2_relat_1(B_481)) | ~v1_relat_1(B_481))), inference(resolution, [status(thm)], [c_10, c_5585])).
% 12.80/4.31  tff(c_5634, plain, (![B_488]: (v2_funct_2(B_488, k2_relat_1(B_488)) | ~v5_relat_1(B_488, k2_relat_1(B_488)) | ~v1_relat_1(B_488))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.80/4.31  tff(c_5656, plain, (![B_481]: (v2_funct_2(B_481, k2_relat_1(B_481)) | ~v1_relat_1(B_481))), inference(resolution, [status(thm)], [c_5599, c_5634])).
% 12.80/4.31  tff(c_9096, plain, (v2_funct_2('#skF_8', '#skF_5') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_9076, c_5656])).
% 12.80/4.31  tff(c_9118, plain, (v2_funct_2('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5463, c_9096])).
% 12.80/4.31  tff(c_9120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5323, c_9118])).
% 12.80/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.80/4.31  
% 12.80/4.31  Inference rules
% 12.80/4.31  ----------------------
% 12.80/4.31  #Ref     : 3
% 12.80/4.31  #Sup     : 1938
% 12.80/4.31  #Fact    : 0
% 12.80/4.31  #Define  : 0
% 12.80/4.31  #Split   : 23
% 12.80/4.31  #Chain   : 0
% 12.80/4.31  #Close   : 0
% 12.80/4.31  
% 12.80/4.31  Ordering : KBO
% 12.80/4.31  
% 12.80/4.31  Simplification rules
% 12.80/4.31  ----------------------
% 12.80/4.31  #Subsume      : 391
% 12.80/4.31  #Demod        : 1484
% 12.80/4.31  #Tautology    : 678
% 12.80/4.31  #SimpNegUnit  : 54
% 12.80/4.31  #BackRed      : 140
% 12.80/4.31  
% 12.80/4.31  #Partial instantiations: 0
% 12.80/4.31  #Strategies tried      : 1
% 12.80/4.31  
% 12.80/4.31  Timing (in seconds)
% 12.80/4.31  ----------------------
% 12.80/4.31  Preprocessing        : 0.62
% 12.80/4.31  Parsing              : 0.31
% 12.80/4.31  CNF conversion       : 0.05
% 12.80/4.31  Main loop            : 2.74
% 12.80/4.31  Inferencing          : 0.92
% 12.80/4.31  Reduction            : 0.96
% 12.80/4.31  Demodulation         : 0.68
% 12.80/4.31  BG Simplification    : 0.09
% 12.80/4.31  Subsumption          : 0.53
% 12.80/4.31  Abstraction          : 0.10
% 12.80/4.31  MUC search           : 0.00
% 12.80/4.32  Cooper               : 0.00
% 12.80/4.32  Total                : 3.44
% 12.80/4.32  Index Insertion      : 0.00
% 12.80/4.32  Index Deletion       : 0.00
% 12.80/4.32  Index Matching       : 0.00
% 12.80/4.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
