%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:21 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 332 expanded)
%              Number of leaves         :   52 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 ( 983 expanded)
%              Number of equality atoms :   47 (  90 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_155,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_91,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_153,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_143,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_177,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_422,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_xboole_0(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_440,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_422])).

tff(c_447,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_76,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_168,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_90,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_88,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_70,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_42,plain,(
    ! [A_31] : v2_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_91,plain,(
    ! [A_31] : v2_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42])).

tff(c_1326,plain,(
    ! [B_192,D_196,A_197,C_194,E_195,F_193] :
      ( k1_partfun1(A_197,B_192,C_194,D_196,E_195,F_193) = k5_relat_1(E_195,F_193)
      | ~ m1_subset_1(F_193,k1_zfmisc_1(k2_zfmisc_1(C_194,D_196)))
      | ~ v1_funct_1(F_193)
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_192)))
      | ~ v1_funct_1(E_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1330,plain,(
    ! [A_197,B_192,E_195] :
      ( k1_partfun1(A_197,B_192,'#skF_4','#skF_3',E_195,'#skF_6') = k5_relat_1(E_195,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_192)))
      | ~ v1_funct_1(E_195) ) ),
    inference(resolution,[status(thm)],[c_80,c_1326])).

tff(c_1635,plain,(
    ! [A_228,B_229,E_230] :
      ( k1_partfun1(A_228,B_229,'#skF_4','#skF_3',E_230,'#skF_6') = k5_relat_1(E_230,'#skF_6')
      | ~ m1_subset_1(E_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(E_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1330])).

tff(c_1647,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_1635])).

tff(c_1661,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1647])).

tff(c_60,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( m1_subset_1(k1_partfun1(A_49,B_50,C_51,D_52,E_53,F_54),k1_zfmisc_1(k2_zfmisc_1(A_49,D_52)))
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(C_51,D_52)))
      | ~ v1_funct_1(F_54)
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1(E_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1770,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1661,c_60])).

tff(c_1777,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_1770])).

tff(c_66,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_78,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1070,plain,(
    ! [D_159,C_160,A_161,B_162] :
      ( D_159 = C_160
      | ~ r2_relset_1(A_161,B_162,C_160,D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1076,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_78,c_1070])).

tff(c_1087,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1076])).

tff(c_1138,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1087])).

tff(c_1971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_1661,c_1138])).

tff(c_1972,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1087])).

tff(c_2582,plain,(
    ! [C_323,A_325,D_327,E_326,B_324] :
      ( k1_xboole_0 = C_323
      | v2_funct_1(D_327)
      | ~ v2_funct_1(k1_partfun1(A_325,B_324,B_324,C_323,D_327,E_326))
      | ~ m1_subset_1(E_326,k1_zfmisc_1(k2_zfmisc_1(B_324,C_323)))
      | ~ v1_funct_2(E_326,B_324,C_323)
      | ~ v1_funct_1(E_326)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324)))
      | ~ v1_funct_2(D_327,A_325,B_324)
      | ~ v1_funct_1(D_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2584,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1972,c_2582])).

tff(c_2586,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_91,c_2584])).

tff(c_2587,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_2586])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2633,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2587,c_2])).

tff(c_2635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_2633])).

tff(c_2637,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2653,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2637,c_4])).

tff(c_2636,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_2645,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2636,c_4])).

tff(c_2676,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2645])).

tff(c_2687,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_168])).

tff(c_2928,plain,(
    ! [A_343] :
      ( v1_xboole_0(k6_partfun1(A_343))
      | ~ v1_xboole_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_66,c_422])).

tff(c_2666,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2645,c_4])).

tff(c_2794,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_2666])).

tff(c_2985,plain,(
    ! [A_347] :
      ( k6_partfun1(A_347) = '#skF_3'
      | ~ v1_xboole_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_2928,c_2794])).

tff(c_2996,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2637,c_2985])).

tff(c_3036,plain,(
    v2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2996,c_91])).

tff(c_3052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2687,c_3036])).

tff(c_3053,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3141,plain,(
    ! [B_359,A_360] :
      ( v1_relat_1(B_359)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(A_360))
      | ~ v1_relat_1(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3153,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_80,c_3141])).

tff(c_3165,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3153])).

tff(c_3222,plain,(
    ! [C_370,B_371,A_372] :
      ( v5_relat_1(C_370,B_371)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_372,B_371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3241,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3222])).

tff(c_3150,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_3141])).

tff(c_3162,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3150])).

tff(c_34,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_4171,plain,(
    ! [D_460,F_457,C_458,A_461,B_456,E_459] :
      ( k1_partfun1(A_461,B_456,C_458,D_460,E_459,F_457) = k5_relat_1(E_459,F_457)
      | ~ m1_subset_1(F_457,k1_zfmisc_1(k2_zfmisc_1(C_458,D_460)))
      | ~ v1_funct_1(F_457)
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(A_461,B_456)))
      | ~ v1_funct_1(E_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4177,plain,(
    ! [A_461,B_456,E_459] :
      ( k1_partfun1(A_461,B_456,'#skF_4','#skF_3',E_459,'#skF_6') = k5_relat_1(E_459,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(A_461,B_456)))
      | ~ v1_funct_1(E_459) ) ),
    inference(resolution,[status(thm)],[c_80,c_4171])).

tff(c_4495,plain,(
    ! [A_492,B_493,E_494] :
      ( k1_partfun1(A_492,B_493,'#skF_4','#skF_3',E_494,'#skF_6') = k5_relat_1(E_494,'#skF_6')
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(A_492,B_493)))
      | ~ v1_funct_1(E_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4177])).

tff(c_4504,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_4495])).

tff(c_4518,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4504])).

tff(c_4632,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4518,c_60])).

tff(c_4638,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_4632])).

tff(c_3915,plain,(
    ! [D_424,C_425,A_426,B_427] :
      ( D_424 = C_425
      | ~ r2_relset_1(A_426,B_427,C_425,D_424)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427)))
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3921,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_78,c_3915])).

tff(c_3932,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3921])).

tff(c_5593,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4638,c_4518,c_4518,c_3932])).

tff(c_30,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_16,B_18)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5617,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5593,c_30])).

tff(c_5625,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3162,c_3165,c_92,c_5617])).

tff(c_3248,plain,(
    ! [B_377,A_378] :
      ( r1_tarski(k2_relat_1(B_377),A_378)
      | ~ v5_relat_1(B_377,A_378)
      | ~ v1_relat_1(B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3264,plain,(
    ! [B_377,A_378] :
      ( k2_relat_1(B_377) = A_378
      | ~ r1_tarski(A_378,k2_relat_1(B_377))
      | ~ v5_relat_1(B_377,A_378)
      | ~ v1_relat_1(B_377) ) ),
    inference(resolution,[status(thm)],[c_3248,c_6])).

tff(c_5634,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5625,c_3264])).

tff(c_5644,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_3241,c_5634])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3188,plain,(
    ! [B_366,A_367] :
      ( v5_relat_1(B_366,A_367)
      | ~ r1_tarski(k2_relat_1(B_366),A_367)
      | ~ v1_relat_1(B_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3206,plain,(
    ! [B_366] :
      ( v5_relat_1(B_366,k2_relat_1(B_366))
      | ~ v1_relat_1(B_366) ) ),
    inference(resolution,[status(thm)],[c_10,c_3188])).

tff(c_3332,plain,(
    ! [B_387] :
      ( v2_funct_2(B_387,k2_relat_1(B_387))
      | ~ v5_relat_1(B_387,k2_relat_1(B_387))
      | ~ v1_relat_1(B_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3359,plain,(
    ! [B_366] :
      ( v2_funct_2(B_366,k2_relat_1(B_366))
      | ~ v1_relat_1(B_366) ) ),
    inference(resolution,[status(thm)],[c_3206,c_3332])).

tff(c_5687,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5644,c_3359])).

tff(c_5725,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_5687])).

tff(c_5727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3053,c_5725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:41:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.27  
% 6.41/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.27  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 6.41/2.27  
% 6.41/2.27  %Foreground sorts:
% 6.41/2.27  
% 6.41/2.27  
% 6.41/2.27  %Background operators:
% 6.41/2.27  
% 6.41/2.27  
% 6.41/2.27  %Foreground operators:
% 6.41/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.41/2.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.41/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.41/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.41/2.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.41/2.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.41/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.41/2.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.41/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.41/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.41/2.27  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.41/2.27  tff('#skF_5', type, '#skF_5': $i).
% 6.41/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.41/2.27  tff('#skF_6', type, '#skF_6': $i).
% 6.41/2.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.41/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.41/2.27  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.41/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.41/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.41/2.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.41/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.41/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.41/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.41/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.41/2.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.41/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.41/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.41/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.41/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.41/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.41/2.27  
% 6.41/2.29  tff(f_197, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.41/2.29  tff(f_104, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.41/2.29  tff(f_155, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.41/2.29  tff(f_91, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.41/2.29  tff(f_153, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.41/2.29  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.41/2.29  tff(f_143, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.41/2.29  tff(f_119, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.41/2.29  tff(f_177, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.41/2.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.41/2.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.41/2.29  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.41/2.29  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.41/2.29  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.41/2.29  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.41/2.29  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 6.41/2.29  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.41/2.29  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.41/2.29  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.41/2.29  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_422, plain, (![C_117, A_118, B_119]: (v1_xboole_0(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.41/2.29  tff(c_440, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_86, c_422])).
% 6.41/2.29  tff(c_447, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_440])).
% 6.41/2.29  tff(c_76, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_168, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_76])).
% 6.41/2.29  tff(c_90, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_88, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_70, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.29  tff(c_42, plain, (![A_31]: (v2_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.41/2.29  tff(c_91, plain, (![A_31]: (v2_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42])).
% 6.41/2.29  tff(c_1326, plain, (![B_192, D_196, A_197, C_194, E_195, F_193]: (k1_partfun1(A_197, B_192, C_194, D_196, E_195, F_193)=k5_relat_1(E_195, F_193) | ~m1_subset_1(F_193, k1_zfmisc_1(k2_zfmisc_1(C_194, D_196))) | ~v1_funct_1(F_193) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_192))) | ~v1_funct_1(E_195))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.41/2.29  tff(c_1330, plain, (![A_197, B_192, E_195]: (k1_partfun1(A_197, B_192, '#skF_4', '#skF_3', E_195, '#skF_6')=k5_relat_1(E_195, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_192))) | ~v1_funct_1(E_195))), inference(resolution, [status(thm)], [c_80, c_1326])).
% 6.41/2.29  tff(c_1635, plain, (![A_228, B_229, E_230]: (k1_partfun1(A_228, B_229, '#skF_4', '#skF_3', E_230, '#skF_6')=k5_relat_1(E_230, '#skF_6') | ~m1_subset_1(E_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(E_230))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1330])).
% 6.41/2.29  tff(c_1647, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_1635])).
% 6.41/2.29  tff(c_1661, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1647])).
% 6.41/2.29  tff(c_60, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (m1_subset_1(k1_partfun1(A_49, B_50, C_51, D_52, E_53, F_54), k1_zfmisc_1(k2_zfmisc_1(A_49, D_52))) | ~m1_subset_1(F_54, k1_zfmisc_1(k2_zfmisc_1(C_51, D_52))) | ~v1_funct_1(F_54) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1(E_53))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.41/2.29  tff(c_1770, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1661, c_60])).
% 6.41/2.29  tff(c_1777, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_1770])).
% 6.41/2.29  tff(c_66, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.41/2.29  tff(c_78, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.41/2.29  tff(c_1070, plain, (![D_159, C_160, A_161, B_162]: (D_159=C_160 | ~r2_relset_1(A_161, B_162, C_160, D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.41/2.29  tff(c_1076, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_78, c_1070])).
% 6.41/2.29  tff(c_1087, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1076])).
% 6.41/2.29  tff(c_1138, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1087])).
% 6.41/2.29  tff(c_1971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1777, c_1661, c_1138])).
% 6.41/2.29  tff(c_1972, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1087])).
% 6.41/2.29  tff(c_2582, plain, (![C_323, A_325, D_327, E_326, B_324]: (k1_xboole_0=C_323 | v2_funct_1(D_327) | ~v2_funct_1(k1_partfun1(A_325, B_324, B_324, C_323, D_327, E_326)) | ~m1_subset_1(E_326, k1_zfmisc_1(k2_zfmisc_1(B_324, C_323))) | ~v1_funct_2(E_326, B_324, C_323) | ~v1_funct_1(E_326) | ~m1_subset_1(D_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_324))) | ~v1_funct_2(D_327, A_325, B_324) | ~v1_funct_1(D_327))), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.41/2.29  tff(c_2584, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1972, c_2582])).
% 6.41/2.29  tff(c_2586, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_91, c_2584])).
% 6.41/2.29  tff(c_2587, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_168, c_2586])).
% 6.41/2.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.41/2.29  tff(c_2633, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2587, c_2])).
% 6.41/2.29  tff(c_2635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_2633])).
% 6.41/2.29  tff(c_2637, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_440])).
% 6.41/2.29  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.41/2.29  tff(c_2653, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2637, c_4])).
% 6.41/2.29  tff(c_2636, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_440])).
% 6.41/2.29  tff(c_2645, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2636, c_4])).
% 6.41/2.29  tff(c_2676, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2645])).
% 6.41/2.29  tff(c_2687, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2676, c_168])).
% 6.41/2.29  tff(c_2928, plain, (![A_343]: (v1_xboole_0(k6_partfun1(A_343)) | ~v1_xboole_0(A_343))), inference(resolution, [status(thm)], [c_66, c_422])).
% 6.41/2.29  tff(c_2666, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2645, c_4])).
% 6.41/2.29  tff(c_2794, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2676, c_2666])).
% 6.41/2.29  tff(c_2985, plain, (![A_347]: (k6_partfun1(A_347)='#skF_3' | ~v1_xboole_0(A_347))), inference(resolution, [status(thm)], [c_2928, c_2794])).
% 6.41/2.29  tff(c_2996, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2637, c_2985])).
% 6.41/2.29  tff(c_3036, plain, (v2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2996, c_91])).
% 6.41/2.29  tff(c_3052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2687, c_3036])).
% 6.41/2.29  tff(c_3053, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 6.41/2.29  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.41/2.29  tff(c_3141, plain, (![B_359, A_360]: (v1_relat_1(B_359) | ~m1_subset_1(B_359, k1_zfmisc_1(A_360)) | ~v1_relat_1(A_360))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.41/2.29  tff(c_3153, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_3141])).
% 6.41/2.29  tff(c_3165, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3153])).
% 6.41/2.29  tff(c_3222, plain, (![C_370, B_371, A_372]: (v5_relat_1(C_370, B_371) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_372, B_371))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.41/2.29  tff(c_3241, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_3222])).
% 6.41/2.29  tff(c_3150, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_3141])).
% 6.41/2.29  tff(c_3162, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3150])).
% 6.41/2.29  tff(c_34, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.41/2.29  tff(c_92, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_34])).
% 6.41/2.29  tff(c_4171, plain, (![D_460, F_457, C_458, A_461, B_456, E_459]: (k1_partfun1(A_461, B_456, C_458, D_460, E_459, F_457)=k5_relat_1(E_459, F_457) | ~m1_subset_1(F_457, k1_zfmisc_1(k2_zfmisc_1(C_458, D_460))) | ~v1_funct_1(F_457) | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(A_461, B_456))) | ~v1_funct_1(E_459))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.41/2.29  tff(c_4177, plain, (![A_461, B_456, E_459]: (k1_partfun1(A_461, B_456, '#skF_4', '#skF_3', E_459, '#skF_6')=k5_relat_1(E_459, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(A_461, B_456))) | ~v1_funct_1(E_459))), inference(resolution, [status(thm)], [c_80, c_4171])).
% 6.41/2.29  tff(c_4495, plain, (![A_492, B_493, E_494]: (k1_partfun1(A_492, B_493, '#skF_4', '#skF_3', E_494, '#skF_6')=k5_relat_1(E_494, '#skF_6') | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(A_492, B_493))) | ~v1_funct_1(E_494))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4177])).
% 6.41/2.29  tff(c_4504, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_4495])).
% 6.41/2.29  tff(c_4518, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4504])).
% 6.41/2.29  tff(c_4632, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4518, c_60])).
% 6.41/2.29  tff(c_4638, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_4632])).
% 6.41/2.29  tff(c_3915, plain, (![D_424, C_425, A_426, B_427]: (D_424=C_425 | ~r2_relset_1(A_426, B_427, C_425, D_424) | ~m1_subset_1(D_424, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.41/2.29  tff(c_3921, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_78, c_3915])).
% 6.41/2.29  tff(c_3932, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3921])).
% 6.41/2.29  tff(c_5593, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4638, c_4518, c_4518, c_3932])).
% 6.41/2.29  tff(c_30, plain, (![A_16, B_18]: (r1_tarski(k2_relat_1(k5_relat_1(A_16, B_18)), k2_relat_1(B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.41/2.29  tff(c_5617, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5593, c_30])).
% 6.41/2.29  tff(c_5625, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3162, c_3165, c_92, c_5617])).
% 6.41/2.29  tff(c_3248, plain, (![B_377, A_378]: (r1_tarski(k2_relat_1(B_377), A_378) | ~v5_relat_1(B_377, A_378) | ~v1_relat_1(B_377))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.29  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.41/2.29  tff(c_3264, plain, (![B_377, A_378]: (k2_relat_1(B_377)=A_378 | ~r1_tarski(A_378, k2_relat_1(B_377)) | ~v5_relat_1(B_377, A_378) | ~v1_relat_1(B_377))), inference(resolution, [status(thm)], [c_3248, c_6])).
% 6.41/2.29  tff(c_5634, plain, (k2_relat_1('#skF_6')='#skF_3' | ~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5625, c_3264])).
% 6.41/2.29  tff(c_5644, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_3241, c_5634])).
% 6.41/2.29  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.41/2.29  tff(c_3188, plain, (![B_366, A_367]: (v5_relat_1(B_366, A_367) | ~r1_tarski(k2_relat_1(B_366), A_367) | ~v1_relat_1(B_366))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.29  tff(c_3206, plain, (![B_366]: (v5_relat_1(B_366, k2_relat_1(B_366)) | ~v1_relat_1(B_366))), inference(resolution, [status(thm)], [c_10, c_3188])).
% 6.41/2.29  tff(c_3332, plain, (![B_387]: (v2_funct_2(B_387, k2_relat_1(B_387)) | ~v5_relat_1(B_387, k2_relat_1(B_387)) | ~v1_relat_1(B_387))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.41/2.29  tff(c_3359, plain, (![B_366]: (v2_funct_2(B_366, k2_relat_1(B_366)) | ~v1_relat_1(B_366))), inference(resolution, [status(thm)], [c_3206, c_3332])).
% 6.41/2.29  tff(c_5687, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5644, c_3359])).
% 6.41/2.29  tff(c_5725, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_5687])).
% 6.41/2.29  tff(c_5727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3053, c_5725])).
% 6.41/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.29  
% 6.41/2.29  Inference rules
% 6.41/2.29  ----------------------
% 6.41/2.29  #Ref     : 0
% 6.41/2.29  #Sup     : 1233
% 6.41/2.29  #Fact    : 0
% 6.41/2.29  #Define  : 0
% 6.41/2.29  #Split   : 12
% 6.41/2.29  #Chain   : 0
% 6.41/2.29  #Close   : 0
% 6.41/2.29  
% 6.41/2.29  Ordering : KBO
% 6.41/2.29  
% 6.41/2.29  Simplification rules
% 6.41/2.29  ----------------------
% 6.41/2.29  #Subsume      : 226
% 6.41/2.29  #Demod        : 1061
% 6.41/2.29  #Tautology    : 427
% 6.41/2.29  #SimpNegUnit  : 12
% 6.41/2.29  #BackRed      : 107
% 6.41/2.29  
% 6.41/2.29  #Partial instantiations: 0
% 6.41/2.29  #Strategies tried      : 1
% 6.41/2.29  
% 6.41/2.29  Timing (in seconds)
% 6.41/2.29  ----------------------
% 6.41/2.29  Preprocessing        : 0.38
% 6.41/2.29  Parsing              : 0.21
% 6.41/2.29  CNF conversion       : 0.03
% 6.41/2.29  Main loop            : 1.15
% 6.41/2.29  Inferencing          : 0.38
% 6.41/2.29  Reduction            : 0.42
% 6.41/2.29  Demodulation         : 0.30
% 6.41/2.29  BG Simplification    : 0.04
% 6.41/2.30  Subsumption          : 0.21
% 6.41/2.30  Abstraction          : 0.05
% 6.41/2.30  MUC search           : 0.00
% 6.41/2.30  Cooper               : 0.00
% 6.41/2.30  Total                : 1.58
% 6.41/2.30  Index Insertion      : 0.00
% 6.41/2.30  Index Deletion       : 0.00
% 6.41/2.30  Index Matching       : 0.00
% 6.41/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
