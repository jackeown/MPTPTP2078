%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 10.80s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 117 expanded)
%              Number of leaves         :   49 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 219 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_14 > #skF_13 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    k1_funct_1('#skF_14','#skF_13') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_116,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_11',k1_tarski('#skF_12')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_380,plain,(
    ! [C_191,B_192,A_193] :
      ( v5_relat_1(C_191,B_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_389,plain,(
    v5_relat_1('#skF_14',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_116,c_380])).

tff(c_220,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_224,plain,(
    v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_116,c_220])).

tff(c_70,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v5_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_114,plain,(
    r2_hidden('#skF_13','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_120,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_118,plain,(
    v1_funct_2('#skF_14','#skF_11',k1_tarski('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_618,plain,(
    ! [A_263,B_264,C_265] :
      ( k1_relset_1(A_263,B_264,C_265) = k1_relat_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_627,plain,(
    k1_relset_1('#skF_11',k1_tarski('#skF_12'),'#skF_14') = k1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_116,c_618])).

tff(c_1491,plain,(
    ! [B_421,A_422,C_423] :
      ( k1_xboole_0 = B_421
      | k1_relset_1(A_422,B_421,C_423) = A_422
      | ~ v1_funct_2(C_423,A_422,B_421)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_422,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1506,plain,
    ( k1_tarski('#skF_12') = k1_xboole_0
    | k1_relset_1('#skF_11',k1_tarski('#skF_12'),'#skF_14') = '#skF_11'
    | ~ v1_funct_2('#skF_14','#skF_11',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_116,c_1491])).

tff(c_1512,plain,
    ( k1_tarski('#skF_12') = k1_xboole_0
    | k1_relat_1('#skF_14') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_627,c_1506])).

tff(c_1513,plain,(
    k1_relat_1('#skF_14') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_1512])).

tff(c_177,plain,(
    ! [C_107,A_108] :
      ( r2_hidden(C_107,k1_zfmisc_1(A_108))
      | ~ r1_tarski(C_107,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_189,plain,(
    ! [C_107,A_108] :
      ( m1_subset_1(C_107,k1_zfmisc_1(A_108))
      | ~ r1_tarski(C_107,A_108) ) ),
    inference(resolution,[status(thm)],[c_177,c_66])).

tff(c_944,plain,(
    ! [A_363,D_364] :
      ( r2_hidden(k1_funct_1(A_363,D_364),k2_relat_1(A_363))
      | ~ r2_hidden(D_364,k1_relat_1(A_363))
      | ~ v1_funct_1(A_363)
      | ~ v1_relat_1(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [C_29,A_26,B_27] :
      ( r2_hidden(C_29,A_26)
      | ~ r2_hidden(C_29,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8335,plain,(
    ! [A_14842,D_14843,A_14844] :
      ( r2_hidden(k1_funct_1(A_14842,D_14843),A_14844)
      | ~ m1_subset_1(k2_relat_1(A_14842),k1_zfmisc_1(A_14844))
      | ~ r2_hidden(D_14843,k1_relat_1(A_14842))
      | ~ v1_funct_1(A_14842)
      | ~ v1_relat_1(A_14842) ) ),
    inference(resolution,[status(thm)],[c_944,c_64])).

tff(c_9444,plain,(
    ! [A_14916,D_14917,A_14918] :
      ( r2_hidden(k1_funct_1(A_14916,D_14917),A_14918)
      | ~ r2_hidden(D_14917,k1_relat_1(A_14916))
      | ~ v1_funct_1(A_14916)
      | ~ v1_relat_1(A_14916)
      | ~ r1_tarski(k2_relat_1(A_14916),A_14918) ) ),
    inference(resolution,[status(thm)],[c_189,c_8335])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10651,plain,(
    ! [A_14987,D_14988,A_14989] :
      ( k1_funct_1(A_14987,D_14988) = A_14989
      | ~ r2_hidden(D_14988,k1_relat_1(A_14987))
      | ~ v1_funct_1(A_14987)
      | ~ v1_relat_1(A_14987)
      | ~ r1_tarski(k2_relat_1(A_14987),k1_tarski(A_14989)) ) ),
    inference(resolution,[status(thm)],[c_9444,c_4])).

tff(c_10735,plain,(
    ! [D_14988,A_14989] :
      ( k1_funct_1('#skF_14',D_14988) = A_14989
      | ~ r2_hidden(D_14988,'#skF_11')
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_tarski(A_14989)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_10651])).

tff(c_10840,plain,(
    ! [D_14993,A_14994] :
      ( k1_funct_1('#skF_14',D_14993) = A_14994
      | ~ r2_hidden(D_14993,'#skF_11')
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_tarski(A_14994)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_120,c_10735])).

tff(c_10973,plain,(
    ! [A_14995] :
      ( k1_funct_1('#skF_14','#skF_13') = A_14995
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_tarski(A_14995)) ) ),
    inference(resolution,[status(thm)],[c_114,c_10840])).

tff(c_10976,plain,(
    ! [A_14995] :
      ( k1_funct_1('#skF_14','#skF_13') = A_14995
      | ~ v5_relat_1('#skF_14',k1_tarski(A_14995))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_70,c_10973])).

tff(c_10980,plain,(
    ! [A_14996] :
      ( k1_funct_1('#skF_14','#skF_13') = A_14996
      | ~ v5_relat_1('#skF_14',k1_tarski(A_14996)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_10976])).

tff(c_10983,plain,(
    k1_funct_1('#skF_14','#skF_13') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_389,c_10980])).

tff(c_10987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_10983])).

tff(c_10988,plain,(
    k1_tarski('#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1512])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_148,plain,(
    ! [B_96,A_97] :
      ( ~ r1_tarski(B_96,A_97)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_155,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_11006,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_10988,c_155])).

tff(c_11022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:27 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.80/3.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.80/3.77  
% 10.80/3.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.80/3.77  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_14 > #skF_13 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_4 > #skF_10
% 10.80/3.77  
% 10.80/3.77  %Foreground sorts:
% 10.80/3.77  
% 10.80/3.77  
% 10.80/3.77  %Background operators:
% 10.80/3.77  
% 10.80/3.77  
% 10.80/3.77  %Foreground operators:
% 10.80/3.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.80/3.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.80/3.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.80/3.77  tff('#skF_11', type, '#skF_11': $i).
% 10.80/3.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.80/3.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.80/3.77  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 10.80/3.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 10.80/3.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.80/3.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.80/3.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.80/3.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.80/3.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.80/3.77  tff('#skF_14', type, '#skF_14': $i).
% 10.80/3.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.80/3.77  tff('#skF_13', type, '#skF_13': $i).
% 10.80/3.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.80/3.77  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.80/3.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.80/3.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.80/3.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.80/3.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.80/3.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.80/3.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.80/3.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.80/3.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.80/3.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.80/3.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.80/3.77  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.80/3.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.80/3.77  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 10.80/3.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.80/3.77  tff('#skF_12', type, '#skF_12': $i).
% 10.80/3.77  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.80/3.77  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 10.80/3.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.80/3.77  
% 10.93/3.79  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.93/3.79  tff(f_145, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 10.93/3.79  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.93/3.79  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.93/3.79  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.93/3.79  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.93/3.79  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.93/3.79  tff(f_47, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.93/3.79  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 10.93/3.79  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 10.93/3.79  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.93/3.79  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 10.93/3.79  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.93/3.79  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.93/3.79  tff(c_112, plain, (k1_funct_1('#skF_14', '#skF_13')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.93/3.79  tff(c_116, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_11', k1_tarski('#skF_12'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.93/3.79  tff(c_380, plain, (![C_191, B_192, A_193]: (v5_relat_1(C_191, B_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.93/3.79  tff(c_389, plain, (v5_relat_1('#skF_14', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_116, c_380])).
% 10.93/3.79  tff(c_220, plain, (![C_131, A_132, B_133]: (v1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.93/3.79  tff(c_224, plain, (v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_116, c_220])).
% 10.93/3.79  tff(c_70, plain, (![B_33, A_32]: (r1_tarski(k2_relat_1(B_33), A_32) | ~v5_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.93/3.79  tff(c_114, plain, (r2_hidden('#skF_13', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.93/3.79  tff(c_120, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.93/3.79  tff(c_118, plain, (v1_funct_2('#skF_14', '#skF_11', k1_tarski('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.93/3.79  tff(c_618, plain, (![A_263, B_264, C_265]: (k1_relset_1(A_263, B_264, C_265)=k1_relat_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.93/3.79  tff(c_627, plain, (k1_relset_1('#skF_11', k1_tarski('#skF_12'), '#skF_14')=k1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_116, c_618])).
% 10.93/3.79  tff(c_1491, plain, (![B_421, A_422, C_423]: (k1_xboole_0=B_421 | k1_relset_1(A_422, B_421, C_423)=A_422 | ~v1_funct_2(C_423, A_422, B_421) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_422, B_421))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.93/3.79  tff(c_1506, plain, (k1_tarski('#skF_12')=k1_xboole_0 | k1_relset_1('#skF_11', k1_tarski('#skF_12'), '#skF_14')='#skF_11' | ~v1_funct_2('#skF_14', '#skF_11', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_116, c_1491])).
% 10.93/3.79  tff(c_1512, plain, (k1_tarski('#skF_12')=k1_xboole_0 | k1_relat_1('#skF_14')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_627, c_1506])).
% 10.93/3.79  tff(c_1513, plain, (k1_relat_1('#skF_14')='#skF_11'), inference(splitLeft, [status(thm)], [c_1512])).
% 10.93/3.79  tff(c_177, plain, (![C_107, A_108]: (r2_hidden(C_107, k1_zfmisc_1(A_108)) | ~r1_tarski(C_107, A_108))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.93/3.79  tff(c_66, plain, (![A_30, B_31]: (m1_subset_1(A_30, B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.93/3.79  tff(c_189, plain, (![C_107, A_108]: (m1_subset_1(C_107, k1_zfmisc_1(A_108)) | ~r1_tarski(C_107, A_108))), inference(resolution, [status(thm)], [c_177, c_66])).
% 10.93/3.79  tff(c_944, plain, (![A_363, D_364]: (r2_hidden(k1_funct_1(A_363, D_364), k2_relat_1(A_363)) | ~r2_hidden(D_364, k1_relat_1(A_363)) | ~v1_funct_1(A_363) | ~v1_relat_1(A_363))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.93/3.79  tff(c_64, plain, (![C_29, A_26, B_27]: (r2_hidden(C_29, A_26) | ~r2_hidden(C_29, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.93/3.79  tff(c_8335, plain, (![A_14842, D_14843, A_14844]: (r2_hidden(k1_funct_1(A_14842, D_14843), A_14844) | ~m1_subset_1(k2_relat_1(A_14842), k1_zfmisc_1(A_14844)) | ~r2_hidden(D_14843, k1_relat_1(A_14842)) | ~v1_funct_1(A_14842) | ~v1_relat_1(A_14842))), inference(resolution, [status(thm)], [c_944, c_64])).
% 10.93/3.79  tff(c_9444, plain, (![A_14916, D_14917, A_14918]: (r2_hidden(k1_funct_1(A_14916, D_14917), A_14918) | ~r2_hidden(D_14917, k1_relat_1(A_14916)) | ~v1_funct_1(A_14916) | ~v1_relat_1(A_14916) | ~r1_tarski(k2_relat_1(A_14916), A_14918))), inference(resolution, [status(thm)], [c_189, c_8335])).
% 10.93/3.79  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.93/3.79  tff(c_10651, plain, (![A_14987, D_14988, A_14989]: (k1_funct_1(A_14987, D_14988)=A_14989 | ~r2_hidden(D_14988, k1_relat_1(A_14987)) | ~v1_funct_1(A_14987) | ~v1_relat_1(A_14987) | ~r1_tarski(k2_relat_1(A_14987), k1_tarski(A_14989)))), inference(resolution, [status(thm)], [c_9444, c_4])).
% 10.93/3.79  tff(c_10735, plain, (![D_14988, A_14989]: (k1_funct_1('#skF_14', D_14988)=A_14989 | ~r2_hidden(D_14988, '#skF_11') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r1_tarski(k2_relat_1('#skF_14'), k1_tarski(A_14989)))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_10651])).
% 10.93/3.79  tff(c_10840, plain, (![D_14993, A_14994]: (k1_funct_1('#skF_14', D_14993)=A_14994 | ~r2_hidden(D_14993, '#skF_11') | ~r1_tarski(k2_relat_1('#skF_14'), k1_tarski(A_14994)))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_120, c_10735])).
% 10.93/3.79  tff(c_10973, plain, (![A_14995]: (k1_funct_1('#skF_14', '#skF_13')=A_14995 | ~r1_tarski(k2_relat_1('#skF_14'), k1_tarski(A_14995)))), inference(resolution, [status(thm)], [c_114, c_10840])).
% 10.93/3.79  tff(c_10976, plain, (![A_14995]: (k1_funct_1('#skF_14', '#skF_13')=A_14995 | ~v5_relat_1('#skF_14', k1_tarski(A_14995)) | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_70, c_10973])).
% 10.93/3.79  tff(c_10980, plain, (![A_14996]: (k1_funct_1('#skF_14', '#skF_13')=A_14996 | ~v5_relat_1('#skF_14', k1_tarski(A_14996)))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_10976])).
% 10.93/3.79  tff(c_10983, plain, (k1_funct_1('#skF_14', '#skF_13')='#skF_12'), inference(resolution, [status(thm)], [c_389, c_10980])).
% 10.93/3.79  tff(c_10987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_10983])).
% 10.93/3.79  tff(c_10988, plain, (k1_tarski('#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1512])).
% 10.93/3.79  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.93/3.79  tff(c_148, plain, (![B_96, A_97]: (~r1_tarski(B_96, A_97) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.93/3.79  tff(c_155, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_148])).
% 10.93/3.79  tff(c_11006, plain, (~r1_tarski(k1_xboole_0, '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_10988, c_155])).
% 10.93/3.79  tff(c_11022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_11006])).
% 10.93/3.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/3.79  
% 10.93/3.79  Inference rules
% 10.93/3.79  ----------------------
% 10.93/3.79  #Ref     : 0
% 10.93/3.79  #Sup     : 2770
% 10.93/3.79  #Fact    : 0
% 10.93/3.79  #Define  : 0
% 10.93/3.79  #Split   : 25
% 10.93/3.79  #Chain   : 0
% 10.93/3.79  #Close   : 0
% 10.93/3.79  
% 10.93/3.79  Ordering : KBO
% 10.93/3.79  
% 10.93/3.79  Simplification rules
% 10.93/3.79  ----------------------
% 10.93/3.79  #Subsume      : 240
% 10.93/3.79  #Demod        : 424
% 10.93/3.79  #Tautology    : 248
% 10.93/3.79  #SimpNegUnit  : 19
% 10.93/3.79  #BackRed      : 15
% 10.93/3.79  
% 10.93/3.79  #Partial instantiations: 1192
% 10.93/3.79  #Strategies tried      : 1
% 10.93/3.79  
% 10.93/3.79  Timing (in seconds)
% 10.93/3.79  ----------------------
% 10.93/3.79  Preprocessing        : 0.37
% 10.93/3.79  Parsing              : 0.18
% 10.93/3.79  CNF conversion       : 0.03
% 10.93/3.79  Main loop            : 2.62
% 10.93/3.79  Inferencing          : 0.82
% 10.93/3.79  Reduction            : 0.85
% 10.93/3.79  Demodulation         : 0.60
% 10.93/3.79  BG Simplification    : 0.08
% 10.93/3.79  Subsumption          : 0.67
% 10.93/3.79  Abstraction          : 0.11
% 10.93/3.79  MUC search           : 0.00
% 10.93/3.79  Cooper               : 0.00
% 10.93/3.79  Total                : 3.03
% 10.93/3.79  Index Insertion      : 0.00
% 10.93/3.79  Index Deletion       : 0.00
% 10.93/3.79  Index Matching       : 0.00
% 10.93/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
