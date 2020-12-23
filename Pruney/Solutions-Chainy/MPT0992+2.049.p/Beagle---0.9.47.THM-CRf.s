%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:38 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :  182 (1305 expanded)
%              Number of leaves         :   37 ( 417 expanded)
%              Depth                    :   15
%              Number of atoms          :  305 (4285 expanded)
%              Number of equality atoms :   85 (1585 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2850,plain,(
    ! [C_314,A_315,B_316] :
      ( v1_relat_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2858,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2850])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3412,plain,(
    ! [A_389,B_390,C_391] :
      ( k1_relset_1(A_389,B_390,C_391) = k1_relat_1(C_391)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3426,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3412])).

tff(c_4261,plain,(
    ! [B_463,A_464,C_465] :
      ( k1_xboole_0 = B_463
      | k1_relset_1(A_464,B_463,C_465) = A_464
      | ~ v1_funct_2(C_465,A_464,B_463)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_464,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4270,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_4261])).

tff(c_4283,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3426,c_4270])).

tff(c_4284,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_4283])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4300,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4284,c_24])).

tff(c_4310,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2858,c_4300])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4162,plain,(
    ! [A_456,B_457,C_458,D_459] :
      ( k2_partfun1(A_456,B_457,C_458,D_459) = k7_relat_1(C_458,D_459)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ v1_funct_1(C_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4168,plain,(
    ! [D_459] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_459) = k7_relat_1('#skF_4',D_459)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_4162])).

tff(c_4179,plain,(
    ! [D_459] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_459) = k7_relat_1('#skF_4',D_459) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4168])).

tff(c_993,plain,(
    ! [C_147,A_148,B_149] :
      ( v1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1001,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_993])).

tff(c_1037,plain,(
    ! [C_160,A_161,B_162] :
      ( v4_relat_1(C_160,A_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1047,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1037])).

tff(c_18,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(k7_relat_1(C_8,A_6))
      | ~ v4_relat_1(C_8,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1049,plain,(
    ! [A_6] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_6))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1047,c_18])).

tff(c_1055,plain,(
    ! [A_6] : v1_relat_1(k7_relat_1('#skF_4',A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1049])).

tff(c_1097,plain,(
    ! [C_175,A_176,B_177] :
      ( v4_relat_1(k7_relat_1(C_175,A_176),A_176)
      | ~ v4_relat_1(C_175,B_177)
      | ~ v1_relat_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1099,plain,(
    ! [A_176] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_176),A_176)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1047,c_1097])).

tff(c_1103,plain,(
    ! [A_178] : v4_relat_1(k7_relat_1('#skF_4',A_178),A_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1099])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1110,plain,(
    ! [A_178] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_178),A_178) = k7_relat_1('#skF_4',A_178)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_178)) ) ),
    inference(resolution,[status(thm)],[c_1103,c_20])).

tff(c_1149,plain,(
    ! [A_185] : k7_relat_1(k7_relat_1('#skF_4',A_185),A_185) = k7_relat_1('#skF_4',A_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1110])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1164,plain,(
    ! [A_185] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_185)),A_185)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_22])).

tff(c_1177,plain,(
    ! [A_185] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_185)),A_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1164])).

tff(c_2826,plain,(
    ! [A_310,B_311,C_312,D_313] :
      ( k2_partfun1(A_310,B_311,C_312,D_313) = k7_relat_1(C_312,D_313)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ v1_funct_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2830,plain,(
    ! [D_313] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_313) = k7_relat_1('#skF_4',D_313)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_2826])).

tff(c_2838,plain,(
    ! [D_313] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_313) = k7_relat_1('#skF_4',D_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2830])).

tff(c_2120,plain,(
    ! [A_275,B_276,C_277,D_278] :
      ( k2_partfun1(A_275,B_276,C_277,D_278) = k7_relat_1(C_277,D_278)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2124,plain,(
    ! [D_278] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_278) = k7_relat_1('#skF_4',D_278)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_2120])).

tff(c_2132,plain,(
    ! [D_278] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_278) = k7_relat_1('#skF_4',D_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2124])).

tff(c_2664,plain,(
    ! [A_299,B_300,C_301,D_302] :
      ( m1_subset_1(k2_partfun1(A_299,B_300,C_301,D_302),k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ v1_funct_1(C_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2689,plain,(
    ! [D_278] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_278),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2132,c_2664])).

tff(c_2708,plain,(
    ! [D_303] : m1_subset_1(k7_relat_1('#skF_4',D_303),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2689])).

tff(c_28,plain,(
    ! [C_20,B_19,A_18] :
      ( v5_relat_1(C_20,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2746,plain,(
    ! [D_303] : v5_relat_1(k7_relat_1('#skF_4',D_303),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2708,c_28])).

tff(c_2025,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k2_partfun1(A_264,B_265,C_266,D_267) = k7_relat_1(C_266,D_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265)))
      | ~ v1_funct_1(C_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2029,plain,(
    ! [D_267] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_267) = k7_relat_1('#skF_4',D_267)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_2025])).

tff(c_2037,plain,(
    ! [D_267] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_267) = k7_relat_1('#skF_4',D_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2029])).

tff(c_1930,plain,(
    ! [C_248,A_249,B_250] :
      ( m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ r1_tarski(k2_relat_1(C_248),B_250)
      | ~ r1_tarski(k1_relat_1(C_248),A_249)
      | ~ v1_relat_1(C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_966,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( v1_funct_1(k2_partfun1(A_141,B_142,C_143,D_144))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_968,plain,(
    ! [D_144] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_144))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_966])).

tff(c_975,plain,(
    ! [D_144] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_968])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_93,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_93])).

tff(c_979,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_992,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_979])).

tff(c_1958,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1930,c_992])).

tff(c_1964,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1958])).

tff(c_2046,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_1964])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_2046])).

tff(c_2053,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1958])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2052,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1958])).

tff(c_2054,plain,(
    ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2052])).

tff(c_2057,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_2054])).

tff(c_2060,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2057])).

tff(c_2133,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2132,c_2060])).

tff(c_2753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2746,c_2133])).

tff(c_2754,plain,(
    ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2052])).

tff(c_2839,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2838,c_2754])).

tff(c_2847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_2839])).

tff(c_2848,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_4198,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4179,c_2848])).

tff(c_2849,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_3425,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2849,c_3412])).

tff(c_4187,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4179,c_4179,c_3425])).

tff(c_4197,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4179,c_2849])).

tff(c_4598,plain,(
    ! [B_477,C_478,A_479] :
      ( k1_xboole_0 = B_477
      | v1_funct_2(C_478,A_479,B_477)
      | k1_relset_1(A_479,B_477,C_478) != A_479
      | ~ m1_subset_1(C_478,k1_zfmisc_1(k2_zfmisc_1(A_479,B_477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4601,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4197,c_4598])).

tff(c_4615,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4187,c_4601])).

tff(c_4616,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4198,c_69,c_4615])).

tff(c_4625,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4310,c_4616])).

tff(c_4629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4625])).

tff(c_4630,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4643,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_4630,c_8])).

tff(c_4631,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4636,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_4631])).

tff(c_4642,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_60])).

tff(c_4644,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4643,c_4642])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4652,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_4630,c_6])).

tff(c_4973,plain,(
    ! [C_552,A_553,B_554] :
      ( v1_relat_1(C_552)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_553,B_554))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4978,plain,(
    ! [C_555] :
      ( v1_relat_1(C_555)
      | ~ m1_subset_1(C_555,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4652,c_4973])).

tff(c_4982,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4644,c_4978])).

tff(c_5004,plain,(
    ! [C_563,A_564,B_565] :
      ( v4_relat_1(C_563,A_564)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_564,B_565))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5011,plain,(
    ! [C_566,A_567] :
      ( v4_relat_1(C_566,A_567)
      | ~ m1_subset_1(C_566,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4652,c_5004])).

tff(c_5016,plain,(
    ! [A_571] : v4_relat_1('#skF_4',A_571) ),
    inference(resolution,[status(thm)],[c_4644,c_5011])).

tff(c_5021,plain,(
    ! [A_571] :
      ( k7_relat_1('#skF_4',A_571) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5016,c_20])).

tff(c_5027,plain,(
    ! [A_571] : k7_relat_1('#skF_4',A_571) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4982,c_5021])).

tff(c_5247,plain,(
    ! [A_615,B_616,C_617,D_618] :
      ( k2_partfun1(A_615,B_616,C_617,D_618) = k7_relat_1(C_617,D_618)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_615,B_616)))
      | ~ v1_funct_1(C_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5310,plain,(
    ! [B_635,C_636,D_637] :
      ( k2_partfun1('#skF_1',B_635,C_636,D_637) = k7_relat_1(C_636,D_637)
      | ~ m1_subset_1(C_636,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_636) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4643,c_5247])).

tff(c_5312,plain,(
    ! [B_635,D_637] :
      ( k2_partfun1('#skF_1',B_635,'#skF_4',D_637) = k7_relat_1('#skF_4',D_637)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4644,c_5310])).

tff(c_5315,plain,(
    ! [B_635,D_637] : k2_partfun1('#skF_1',B_635,'#skF_4',D_637) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5027,c_5312])).

tff(c_4952,plain,(
    ! [A_541,B_542,C_543,D_544] :
      ( v1_funct_1(k2_partfun1(A_541,B_542,C_543,D_544))
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542)))
      | ~ v1_funct_1(C_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4962,plain,(
    ! [A_549,C_550,D_551] :
      ( v1_funct_1(k2_partfun1(A_549,'#skF_1',C_550,D_551))
      | ~ m1_subset_1(C_550,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4652,c_4952])).

tff(c_4964,plain,(
    ! [A_549,D_551] :
      ( v1_funct_1(k2_partfun1(A_549,'#skF_1','#skF_4',D_551))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4644,c_4962])).

tff(c_4967,plain,(
    ! [A_549,D_551] : v1_funct_1(k2_partfun1(A_549,'#skF_1','#skF_4',D_551)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4964])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4669,plain,(
    ! [A_482] :
      ( A_482 = '#skF_1'
      | ~ r1_tarski(A_482,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_4630,c_2])).

tff(c_4673,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_4669])).

tff(c_4703,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4673,c_4636,c_4673,c_4673,c_4636,c_4636,c_4673,c_4652,c_4636,c_4636,c_54])).

tff(c_4704,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4703])).

tff(c_4970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4704])).

tff(c_4971,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4703])).

tff(c_5001,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4971])).

tff(c_5317,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_5001])).

tff(c_5321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4644,c_5317])).

tff(c_5323,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4971])).

tff(c_4975,plain,(
    ! [C_552] :
      ( v1_relat_1(C_552)
      | ~ m1_subset_1(C_552,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4652,c_4973])).

tff(c_5329,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5323,c_4975])).

tff(c_5435,plain,(
    ! [C_653,A_654,B_655] :
      ( v4_relat_1(C_653,A_654)
      | ~ m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(A_654,B_655))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5442,plain,(
    ! [C_656,A_657] :
      ( v4_relat_1(C_656,A_657)
      | ~ m1_subset_1(C_656,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4652,c_5435])).

tff(c_5483,plain,(
    ! [A_664] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_664) ),
    inference(resolution,[status(thm)],[c_5323,c_5442])).

tff(c_5488,plain,(
    ! [A_664] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_664) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_5483,c_20])).

tff(c_5551,plain,(
    ! [A_673] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_673) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5329,c_5488])).

tff(c_4674,plain,(
    ! [B_483,A_484] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_483,A_484)),A_484)
      | ~ v1_relat_1(B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4668,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_4630,c_2])).

tff(c_4679,plain,(
    ! [B_483] :
      ( k1_relat_1(k7_relat_1(B_483,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_483) ) ),
    inference(resolution,[status(thm)],[c_4674,c_4668])).

tff(c_5560,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5551,c_4679])).

tff(c_5570,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5329,c_5560])).

tff(c_5610,plain,(
    ! [A_676,B_677,C_678] :
      ( k1_relset_1(A_676,B_677,C_678) = k1_relat_1(C_678)
      | ~ m1_subset_1(C_678,k1_zfmisc_1(k2_zfmisc_1(A_676,B_677))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5641,plain,(
    ! [B_683,C_684] :
      ( k1_relset_1('#skF_1',B_683,C_684) = k1_relat_1(C_684)
      | ~ m1_subset_1(C_684,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4643,c_5610])).

tff(c_5643,plain,(
    ! [B_683] : k1_relset_1('#skF_1',B_683,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5323,c_5641])).

tff(c_5647,plain,(
    ! [B_683] : k1_relset_1('#skF_1',B_683,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5570,c_5643])).

tff(c_40,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40])).

tff(c_5696,plain,(
    ! [C_691,B_692] :
      ( v1_funct_2(C_691,'#skF_1',B_692)
      | k1_relset_1('#skF_1',B_692,C_691) != '#skF_1'
      | ~ m1_subset_1(C_691,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_4630,c_4630,c_4630,c_66])).

tff(c_5698,plain,(
    ! [B_692] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_692)
      | k1_relset_1('#skF_1',B_692,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_5323,c_5696])).

tff(c_5703,plain,(
    ! [B_692] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_692) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5647,c_5698])).

tff(c_5322,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4971])).

tff(c_5723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5703,c_5322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:12:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.12/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.40  
% 6.54/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.55/2.41  
% 6.55/2.41  %Foreground sorts:
% 6.55/2.41  
% 6.55/2.41  
% 6.55/2.41  %Background operators:
% 6.55/2.41  
% 6.55/2.41  
% 6.55/2.41  %Foreground operators:
% 6.55/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.55/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.55/2.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.55/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.55/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.55/2.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.55/2.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.55/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.55/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.55/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.55/2.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.55/2.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.55/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.55/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.55/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.55/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.55/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.55/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.55/2.41  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.55/2.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.55/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.55/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.55/2.41  
% 6.55/2.45  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 6.55/2.45  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.55/2.45  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.55/2.45  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.55/2.45  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 6.55/2.45  tff(f_121, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.55/2.45  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.55/2.45  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 6.55/2.45  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.55/2.45  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 6.55/2.45  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.55/2.45  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 6.55/2.45  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.55/2.45  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.55/2.45  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.55/2.45  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.55/2.45  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.55/2.45  tff(c_2850, plain, (![C_314, A_315, B_316]: (v1_relat_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.55/2.45  tff(c_2858, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2850])).
% 6.55/2.45  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.55/2.45  tff(c_69, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 6.55/2.45  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.55/2.45  tff(c_3412, plain, (![A_389, B_390, C_391]: (k1_relset_1(A_389, B_390, C_391)=k1_relat_1(C_391) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.55/2.45  tff(c_3426, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3412])).
% 6.55/2.45  tff(c_4261, plain, (![B_463, A_464, C_465]: (k1_xboole_0=B_463 | k1_relset_1(A_464, B_463, C_465)=A_464 | ~v1_funct_2(C_465, A_464, B_463) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_464, B_463))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.55/2.45  tff(c_4270, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_4261])).
% 6.55/2.45  tff(c_4283, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3426, c_4270])).
% 6.55/2.45  tff(c_4284, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_69, c_4283])).
% 6.55/2.45  tff(c_24, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.55/2.45  tff(c_4300, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4284, c_24])).
% 6.55/2.45  tff(c_4310, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2858, c_4300])).
% 6.55/2.45  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.55/2.45  tff(c_4162, plain, (![A_456, B_457, C_458, D_459]: (k2_partfun1(A_456, B_457, C_458, D_459)=k7_relat_1(C_458, D_459) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~v1_funct_1(C_458))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.55/2.45  tff(c_4168, plain, (![D_459]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_459)=k7_relat_1('#skF_4', D_459) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_4162])).
% 6.55/2.45  tff(c_4179, plain, (![D_459]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_459)=k7_relat_1('#skF_4', D_459))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4168])).
% 6.55/2.45  tff(c_993, plain, (![C_147, A_148, B_149]: (v1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.55/2.45  tff(c_1001, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_993])).
% 6.55/2.45  tff(c_1037, plain, (![C_160, A_161, B_162]: (v4_relat_1(C_160, A_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.55/2.45  tff(c_1047, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1037])).
% 6.55/2.45  tff(c_18, plain, (![C_8, A_6, B_7]: (v1_relat_1(k7_relat_1(C_8, A_6)) | ~v4_relat_1(C_8, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.55/2.45  tff(c_1049, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1047, c_18])).
% 6.55/2.45  tff(c_1055, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1049])).
% 6.55/2.45  tff(c_1097, plain, (![C_175, A_176, B_177]: (v4_relat_1(k7_relat_1(C_175, A_176), A_176) | ~v4_relat_1(C_175, B_177) | ~v1_relat_1(C_175))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.55/2.45  tff(c_1099, plain, (![A_176]: (v4_relat_1(k7_relat_1('#skF_4', A_176), A_176) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1047, c_1097])).
% 6.55/2.45  tff(c_1103, plain, (![A_178]: (v4_relat_1(k7_relat_1('#skF_4', A_178), A_178))), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1099])).
% 6.55/2.45  tff(c_20, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.55/2.45  tff(c_1110, plain, (![A_178]: (k7_relat_1(k7_relat_1('#skF_4', A_178), A_178)=k7_relat_1('#skF_4', A_178) | ~v1_relat_1(k7_relat_1('#skF_4', A_178)))), inference(resolution, [status(thm)], [c_1103, c_20])).
% 6.55/2.45  tff(c_1149, plain, (![A_185]: (k7_relat_1(k7_relat_1('#skF_4', A_185), A_185)=k7_relat_1('#skF_4', A_185))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1110])).
% 6.55/2.45  tff(c_22, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.55/2.45  tff(c_1164, plain, (![A_185]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_185)), A_185) | ~v1_relat_1(k7_relat_1('#skF_4', A_185)))), inference(superposition, [status(thm), theory('equality')], [c_1149, c_22])).
% 6.55/2.45  tff(c_1177, plain, (![A_185]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_185)), A_185))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1164])).
% 6.55/2.45  tff(c_2826, plain, (![A_310, B_311, C_312, D_313]: (k2_partfun1(A_310, B_311, C_312, D_313)=k7_relat_1(C_312, D_313) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~v1_funct_1(C_312))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.55/2.45  tff(c_2830, plain, (![D_313]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_313)=k7_relat_1('#skF_4', D_313) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2826])).
% 6.55/2.45  tff(c_2838, plain, (![D_313]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_313)=k7_relat_1('#skF_4', D_313))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2830])).
% 6.55/2.45  tff(c_2120, plain, (![A_275, B_276, C_277, D_278]: (k2_partfun1(A_275, B_276, C_277, D_278)=k7_relat_1(C_277, D_278) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1(C_277))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.55/2.45  tff(c_2124, plain, (![D_278]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_278)=k7_relat_1('#skF_4', D_278) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2120])).
% 6.55/2.45  tff(c_2132, plain, (![D_278]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_278)=k7_relat_1('#skF_4', D_278))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2124])).
% 6.55/2.45  tff(c_2664, plain, (![A_299, B_300, C_301, D_302]: (m1_subset_1(k2_partfun1(A_299, B_300, C_301, D_302), k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~v1_funct_1(C_301))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.55/2.45  tff(c_2689, plain, (![D_278]: (m1_subset_1(k7_relat_1('#skF_4', D_278), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2132, c_2664])).
% 6.55/2.45  tff(c_2708, plain, (![D_303]: (m1_subset_1(k7_relat_1('#skF_4', D_303), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2689])).
% 6.55/2.45  tff(c_28, plain, (![C_20, B_19, A_18]: (v5_relat_1(C_20, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.55/2.45  tff(c_2746, plain, (![D_303]: (v5_relat_1(k7_relat_1('#skF_4', D_303), '#skF_2'))), inference(resolution, [status(thm)], [c_2708, c_28])).
% 6.55/2.45  tff(c_2025, plain, (![A_264, B_265, C_266, D_267]: (k2_partfun1(A_264, B_265, C_266, D_267)=k7_relat_1(C_266, D_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))) | ~v1_funct_1(C_266))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.55/2.45  tff(c_2029, plain, (![D_267]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_267)=k7_relat_1('#skF_4', D_267) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2025])).
% 6.55/2.45  tff(c_2037, plain, (![D_267]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_267)=k7_relat_1('#skF_4', D_267))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2029])).
% 6.55/2.45  tff(c_1930, plain, (![C_248, A_249, B_250]: (m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~r1_tarski(k2_relat_1(C_248), B_250) | ~r1_tarski(k1_relat_1(C_248), A_249) | ~v1_relat_1(C_248))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.55/2.45  tff(c_966, plain, (![A_141, B_142, C_143, D_144]: (v1_funct_1(k2_partfun1(A_141, B_142, C_143, D_144)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(C_143))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.55/2.45  tff(c_968, plain, (![D_144]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_144)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_966])).
% 6.55/2.45  tff(c_975, plain, (![D_144]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_144)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_968])).
% 6.55/2.45  tff(c_54, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.55/2.45  tff(c_93, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.55/2.45  tff(c_978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_975, c_93])).
% 6.55/2.45  tff(c_979, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 6.55/2.45  tff(c_992, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_979])).
% 6.55/2.45  tff(c_1958, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1930, c_992])).
% 6.55/2.45  tff(c_1964, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1958])).
% 6.55/2.45  tff(c_2046, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_1964])).
% 6.55/2.45  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1055, c_2046])).
% 6.55/2.45  tff(c_2053, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1958])).
% 6.55/2.45  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.55/2.45  tff(c_2052, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1958])).
% 6.55/2.45  tff(c_2054, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_2052])).
% 6.55/2.45  tff(c_2057, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_2054])).
% 6.55/2.45  tff(c_2060, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2057])).
% 6.55/2.45  tff(c_2133, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2132, c_2060])).
% 6.55/2.45  tff(c_2753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2746, c_2133])).
% 6.55/2.45  tff(c_2754, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_2052])).
% 6.55/2.45  tff(c_2839, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2838, c_2754])).
% 6.55/2.45  tff(c_2847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1177, c_2839])).
% 6.55/2.45  tff(c_2848, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_979])).
% 6.55/2.45  tff(c_4198, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4179, c_2848])).
% 6.55/2.45  tff(c_2849, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_979])).
% 6.55/2.45  tff(c_3425, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2849, c_3412])).
% 6.55/2.45  tff(c_4187, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4179, c_4179, c_3425])).
% 6.55/2.45  tff(c_4197, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4179, c_2849])).
% 6.55/2.45  tff(c_4598, plain, (![B_477, C_478, A_479]: (k1_xboole_0=B_477 | v1_funct_2(C_478, A_479, B_477) | k1_relset_1(A_479, B_477, C_478)!=A_479 | ~m1_subset_1(C_478, k1_zfmisc_1(k2_zfmisc_1(A_479, B_477))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.55/2.45  tff(c_4601, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_4197, c_4598])).
% 6.55/2.45  tff(c_4615, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4187, c_4601])).
% 6.55/2.45  tff(c_4616, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4198, c_69, c_4615])).
% 6.55/2.45  tff(c_4625, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4310, c_4616])).
% 6.55/2.45  tff(c_4629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_4625])).
% 6.55/2.45  tff(c_4630, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 6.55/2.45  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.45  tff(c_4643, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_4630, c_8])).
% 6.55/2.45  tff(c_4631, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 6.55/2.45  tff(c_4636, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_4631])).
% 6.55/2.45  tff(c_4642, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_60])).
% 6.55/2.45  tff(c_4644, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4643, c_4642])).
% 6.55/2.45  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.45  tff(c_4652, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_4630, c_6])).
% 6.55/2.45  tff(c_4973, plain, (![C_552, A_553, B_554]: (v1_relat_1(C_552) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(A_553, B_554))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.55/2.45  tff(c_4978, plain, (![C_555]: (v1_relat_1(C_555) | ~m1_subset_1(C_555, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4652, c_4973])).
% 6.55/2.45  tff(c_4982, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4644, c_4978])).
% 6.55/2.45  tff(c_5004, plain, (![C_563, A_564, B_565]: (v4_relat_1(C_563, A_564) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_564, B_565))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.55/2.45  tff(c_5011, plain, (![C_566, A_567]: (v4_relat_1(C_566, A_567) | ~m1_subset_1(C_566, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4652, c_5004])).
% 6.55/2.45  tff(c_5016, plain, (![A_571]: (v4_relat_1('#skF_4', A_571))), inference(resolution, [status(thm)], [c_4644, c_5011])).
% 6.55/2.45  tff(c_5021, plain, (![A_571]: (k7_relat_1('#skF_4', A_571)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5016, c_20])).
% 6.55/2.45  tff(c_5027, plain, (![A_571]: (k7_relat_1('#skF_4', A_571)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4982, c_5021])).
% 6.55/2.45  tff(c_5247, plain, (![A_615, B_616, C_617, D_618]: (k2_partfun1(A_615, B_616, C_617, D_618)=k7_relat_1(C_617, D_618) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_615, B_616))) | ~v1_funct_1(C_617))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.55/2.45  tff(c_5310, plain, (![B_635, C_636, D_637]: (k2_partfun1('#skF_1', B_635, C_636, D_637)=k7_relat_1(C_636, D_637) | ~m1_subset_1(C_636, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_636))), inference(superposition, [status(thm), theory('equality')], [c_4643, c_5247])).
% 6.55/2.45  tff(c_5312, plain, (![B_635, D_637]: (k2_partfun1('#skF_1', B_635, '#skF_4', D_637)=k7_relat_1('#skF_4', D_637) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4644, c_5310])).
% 6.55/2.45  tff(c_5315, plain, (![B_635, D_637]: (k2_partfun1('#skF_1', B_635, '#skF_4', D_637)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5027, c_5312])).
% 6.55/2.45  tff(c_4952, plain, (![A_541, B_542, C_543, D_544]: (v1_funct_1(k2_partfun1(A_541, B_542, C_543, D_544)) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))) | ~v1_funct_1(C_543))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.55/2.45  tff(c_4962, plain, (![A_549, C_550, D_551]: (v1_funct_1(k2_partfun1(A_549, '#skF_1', C_550, D_551)) | ~m1_subset_1(C_550, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_550))), inference(superposition, [status(thm), theory('equality')], [c_4652, c_4952])).
% 6.55/2.45  tff(c_4964, plain, (![A_549, D_551]: (v1_funct_1(k2_partfun1(A_549, '#skF_1', '#skF_4', D_551)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4644, c_4962])).
% 6.55/2.45  tff(c_4967, plain, (![A_549, D_551]: (v1_funct_1(k2_partfun1(A_549, '#skF_1', '#skF_4', D_551)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4964])).
% 6.55/2.45  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.55/2.45  tff(c_4669, plain, (![A_482]: (A_482='#skF_1' | ~r1_tarski(A_482, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_4630, c_2])).
% 6.55/2.45  tff(c_4673, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_58, c_4669])).
% 6.55/2.45  tff(c_4703, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4673, c_4636, c_4673, c_4673, c_4636, c_4636, c_4673, c_4652, c_4636, c_4636, c_54])).
% 6.55/2.45  tff(c_4704, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4703])).
% 6.55/2.45  tff(c_4970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4704])).
% 6.55/2.45  tff(c_4971, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4703])).
% 6.55/2.45  tff(c_5001, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4971])).
% 6.55/2.45  tff(c_5317, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5315, c_5001])).
% 6.55/2.45  tff(c_5321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4644, c_5317])).
% 6.55/2.45  tff(c_5323, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4971])).
% 6.55/2.45  tff(c_4975, plain, (![C_552]: (v1_relat_1(C_552) | ~m1_subset_1(C_552, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4652, c_4973])).
% 6.55/2.45  tff(c_5329, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_5323, c_4975])).
% 6.55/2.45  tff(c_5435, plain, (![C_653, A_654, B_655]: (v4_relat_1(C_653, A_654) | ~m1_subset_1(C_653, k1_zfmisc_1(k2_zfmisc_1(A_654, B_655))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.55/2.45  tff(c_5442, plain, (![C_656, A_657]: (v4_relat_1(C_656, A_657) | ~m1_subset_1(C_656, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4652, c_5435])).
% 6.55/2.45  tff(c_5483, plain, (![A_664]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_664))), inference(resolution, [status(thm)], [c_5323, c_5442])).
% 6.55/2.45  tff(c_5488, plain, (![A_664]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_664)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_5483, c_20])).
% 6.55/2.45  tff(c_5551, plain, (![A_673]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_673)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5329, c_5488])).
% 6.55/2.45  tff(c_4674, plain, (![B_483, A_484]: (r1_tarski(k1_relat_1(k7_relat_1(B_483, A_484)), A_484) | ~v1_relat_1(B_483))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.55/2.45  tff(c_4668, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_4630, c_2])).
% 6.55/2.45  tff(c_4679, plain, (![B_483]: (k1_relat_1(k7_relat_1(B_483, '#skF_1'))='#skF_1' | ~v1_relat_1(B_483))), inference(resolution, [status(thm)], [c_4674, c_4668])).
% 6.55/2.45  tff(c_5560, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5551, c_4679])).
% 6.55/2.45  tff(c_5570, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5329, c_5560])).
% 6.55/2.45  tff(c_5610, plain, (![A_676, B_677, C_678]: (k1_relset_1(A_676, B_677, C_678)=k1_relat_1(C_678) | ~m1_subset_1(C_678, k1_zfmisc_1(k2_zfmisc_1(A_676, B_677))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.55/2.45  tff(c_5641, plain, (![B_683, C_684]: (k1_relset_1('#skF_1', B_683, C_684)=k1_relat_1(C_684) | ~m1_subset_1(C_684, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4643, c_5610])).
% 6.55/2.45  tff(c_5643, plain, (![B_683]: (k1_relset_1('#skF_1', B_683, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_5323, c_5641])).
% 6.55/2.45  tff(c_5647, plain, (![B_683]: (k1_relset_1('#skF_1', B_683, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5570, c_5643])).
% 6.55/2.45  tff(c_40, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.55/2.45  tff(c_66, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_40])).
% 6.55/2.45  tff(c_5696, plain, (![C_691, B_692]: (v1_funct_2(C_691, '#skF_1', B_692) | k1_relset_1('#skF_1', B_692, C_691)!='#skF_1' | ~m1_subset_1(C_691, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_4630, c_4630, c_4630, c_66])).
% 6.55/2.45  tff(c_5698, plain, (![B_692]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_692) | k1_relset_1('#skF_1', B_692, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_5323, c_5696])).
% 6.55/2.45  tff(c_5703, plain, (![B_692]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_692))), inference(demodulation, [status(thm), theory('equality')], [c_5647, c_5698])).
% 6.55/2.45  tff(c_5322, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4971])).
% 6.55/2.45  tff(c_5723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5703, c_5322])).
% 6.55/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.45  
% 6.55/2.45  Inference rules
% 6.55/2.45  ----------------------
% 6.55/2.45  #Ref     : 0
% 6.55/2.45  #Sup     : 1192
% 6.55/2.45  #Fact    : 0
% 6.55/2.45  #Define  : 0
% 6.55/2.45  #Split   : 23
% 6.55/2.45  #Chain   : 0
% 6.55/2.45  #Close   : 0
% 6.55/2.45  
% 6.55/2.45  Ordering : KBO
% 6.55/2.45  
% 6.55/2.45  Simplification rules
% 6.55/2.45  ----------------------
% 6.55/2.45  #Subsume      : 78
% 6.55/2.45  #Demod        : 1477
% 6.55/2.45  #Tautology    : 623
% 6.55/2.45  #SimpNegUnit  : 12
% 6.55/2.45  #BackRed      : 56
% 6.55/2.45  
% 6.55/2.45  #Partial instantiations: 0
% 6.55/2.45  #Strategies tried      : 1
% 6.55/2.45  
% 6.55/2.45  Timing (in seconds)
% 6.55/2.45  ----------------------
% 6.55/2.45  Preprocessing        : 0.37
% 6.55/2.45  Parsing              : 0.20
% 6.55/2.45  CNF conversion       : 0.03
% 6.55/2.45  Main loop            : 1.17
% 6.55/2.45  Inferencing          : 0.40
% 6.55/2.45  Reduction            : 0.44
% 6.55/2.45  Demodulation         : 0.32
% 6.55/2.46  BG Simplification    : 0.04
% 6.55/2.46  Subsumption          : 0.19
% 6.55/2.46  Abstraction          : 0.05
% 6.55/2.46  MUC search           : 0.00
% 6.55/2.46  Cooper               : 0.00
% 6.55/2.46  Total                : 1.64
% 6.55/2.46  Index Insertion      : 0.00
% 6.55/2.46  Index Deletion       : 0.00
% 6.55/2.46  Index Matching       : 0.00
% 6.55/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
