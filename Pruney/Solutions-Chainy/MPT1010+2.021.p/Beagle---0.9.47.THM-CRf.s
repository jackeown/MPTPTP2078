%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 20.31s
% Output     : CNFRefutation 20.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 115 expanded)
%              Number of leaves         :   44 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 223 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_80,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_202,plain,(
    ! [C_108,B_109,A_110] :
      ( v5_relat_1(C_108,B_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_211,plain,(
    v5_relat_1('#skF_10',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_202])).

tff(c_150,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_159,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_150])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_84,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_82,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_367,plain,(
    ! [A_157,B_158,C_159] :
      ( k1_relset_1(A_157,B_158,C_159) = k1_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_376,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_367])).

tff(c_791,plain,(
    ! [B_218,A_219,C_220] :
      ( k1_xboole_0 = B_218
      | k1_relset_1(A_219,B_218,C_220) = A_219
      | ~ v1_funct_2(C_220,A_219,B_218)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_219,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_798,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_791])).

tff(c_802,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_376,c_798])).

tff(c_803,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_427,plain,(
    ! [A_174,D_175] :
      ( r2_hidden(k1_funct_1(A_174,D_175),k2_relat_1(A_174))
      | ~ r2_hidden(D_175,k1_relat_1(A_174))
      | ~ v1_funct_1(A_174)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93512,plain,(
    ! [A_41793,D_41794,A_41795] :
      ( r2_hidden(k1_funct_1(A_41793,D_41794),A_41795)
      | ~ m1_subset_1(k2_relat_1(A_41793),k1_zfmisc_1(A_41795))
      | ~ r2_hidden(D_41794,k1_relat_1(A_41793))
      | ~ v1_funct_1(A_41793)
      | ~ v1_relat_1(A_41793) ) ),
    inference(resolution,[status(thm)],[c_427,c_26])).

tff(c_93575,plain,(
    ! [A_41951,D_41952,B_41953] :
      ( r2_hidden(k1_funct_1(A_41951,D_41952),B_41953)
      | ~ r2_hidden(D_41952,k1_relat_1(A_41951))
      | ~ v1_funct_1(A_41951)
      | ~ v1_relat_1(A_41951)
      | ~ r1_tarski(k2_relat_1(A_41951),B_41953) ) ),
    inference(resolution,[status(thm)],[c_30,c_93512])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_171,plain,(
    ! [D_99,B_100,A_101] :
      ( D_99 = B_100
      | D_99 = A_101
      | ~ r2_hidden(D_99,k2_tarski(A_101,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_180,plain,(
    ! [D_99,A_8] :
      ( D_99 = A_8
      | D_99 = A_8
      | ~ r2_hidden(D_99,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_171])).

tff(c_93787,plain,(
    ! [A_42109,D_42110,A_42111] :
      ( k1_funct_1(A_42109,D_42110) = A_42111
      | ~ r2_hidden(D_42110,k1_relat_1(A_42109))
      | ~ v1_funct_1(A_42109)
      | ~ v1_relat_1(A_42109)
      | ~ r1_tarski(k2_relat_1(A_42109),k1_tarski(A_42111)) ) ),
    inference(resolution,[status(thm)],[c_93575,c_180])).

tff(c_93872,plain,(
    ! [D_42110,A_42111] :
      ( k1_funct_1('#skF_10',D_42110) = A_42111
      | ~ r2_hidden(D_42110,'#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_tarski(A_42111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_93787])).

tff(c_93894,plain,(
    ! [D_42267,A_42268] :
      ( k1_funct_1('#skF_10',D_42267) = A_42268
      | ~ r2_hidden(D_42267,'#skF_7')
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_tarski(A_42268)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_84,c_93872])).

tff(c_94048,plain,(
    ! [A_42424] :
      ( k1_funct_1('#skF_10','#skF_9') = A_42424
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_tarski(A_42424)) ) ),
    inference(resolution,[status(thm)],[c_78,c_93894])).

tff(c_94190,plain,(
    ! [A_42424] :
      ( k1_funct_1('#skF_10','#skF_9') = A_42424
      | ~ v5_relat_1('#skF_10',k1_tarski(A_42424))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_94048])).

tff(c_94195,plain,(
    ! [A_42580] :
      ( k1_funct_1('#skF_10','#skF_9') = A_42580
      | ~ v5_relat_1('#skF_10',k1_tarski(A_42580)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_94190])).

tff(c_94332,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_211,c_94195])).

tff(c_94336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_94332])).

tff(c_94337,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_95,plain,(
    ! [D_75,A_76] : r2_hidden(D_75,k2_tarski(A_76,D_75)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_95])).

tff(c_105,plain,(
    ! [B_80,A_81] :
      ( ~ r1_tarski(B_80,A_81)
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_98,c_105])).

tff(c_94359,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_94337,c_119])).

tff(c_94369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_94359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.31/10.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.31/10.70  
% 20.31/10.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.31/10.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 20.31/10.70  
% 20.31/10.70  %Foreground sorts:
% 20.31/10.70  
% 20.31/10.70  
% 20.31/10.70  %Background operators:
% 20.31/10.70  
% 20.31/10.70  
% 20.31/10.70  %Foreground operators:
% 20.31/10.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.31/10.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.31/10.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.31/10.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.31/10.70  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 20.31/10.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.31/10.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.31/10.70  tff('#skF_7', type, '#skF_7': $i).
% 20.31/10.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.31/10.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.31/10.70  tff('#skF_10', type, '#skF_10': $i).
% 20.31/10.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.31/10.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.31/10.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.31/10.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.31/10.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.31/10.70  tff('#skF_9', type, '#skF_9': $i).
% 20.31/10.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 20.31/10.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 20.31/10.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.31/10.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 20.31/10.70  tff('#skF_8', type, '#skF_8': $i).
% 20.31/10.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.31/10.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.31/10.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.31/10.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.31/10.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 20.31/10.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.31/10.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.31/10.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.31/10.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.31/10.70  
% 20.31/10.71  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 20.31/10.71  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 20.31/10.71  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 20.31/10.71  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 20.31/10.71  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 20.31/10.71  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 20.31/10.71  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 20.31/10.71  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.31/10.71  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 20.31/10.71  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 20.31/10.71  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 20.31/10.71  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 20.31/10.71  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 20.31/10.71  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.31/10.71  tff(c_76, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 20.31/10.71  tff(c_80, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 20.31/10.71  tff(c_202, plain, (![C_108, B_109, A_110]: (v5_relat_1(C_108, B_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.31/10.71  tff(c_211, plain, (v5_relat_1('#skF_10', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_202])).
% 20.31/10.71  tff(c_150, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.31/10.71  tff(c_159, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_150])).
% 20.31/10.71  tff(c_34, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.31/10.71  tff(c_78, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 20.31/10.71  tff(c_84, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_120])).
% 20.31/10.71  tff(c_82, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 20.31/10.71  tff(c_367, plain, (![A_157, B_158, C_159]: (k1_relset_1(A_157, B_158, C_159)=k1_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.31/10.71  tff(c_376, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_367])).
% 20.31/10.71  tff(c_791, plain, (![B_218, A_219, C_220]: (k1_xboole_0=B_218 | k1_relset_1(A_219, B_218, C_220)=A_219 | ~v1_funct_2(C_220, A_219, B_218) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_219, B_218))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 20.31/10.71  tff(c_798, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_791])).
% 20.31/10.71  tff(c_802, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_376, c_798])).
% 20.31/10.71  tff(c_803, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_802])).
% 20.31/10.71  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.31/10.71  tff(c_427, plain, (![A_174, D_175]: (r2_hidden(k1_funct_1(A_174, D_175), k2_relat_1(A_174)) | ~r2_hidden(D_175, k1_relat_1(A_174)) | ~v1_funct_1(A_174) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.31/10.71  tff(c_26, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.31/10.71  tff(c_93512, plain, (![A_41793, D_41794, A_41795]: (r2_hidden(k1_funct_1(A_41793, D_41794), A_41795) | ~m1_subset_1(k2_relat_1(A_41793), k1_zfmisc_1(A_41795)) | ~r2_hidden(D_41794, k1_relat_1(A_41793)) | ~v1_funct_1(A_41793) | ~v1_relat_1(A_41793))), inference(resolution, [status(thm)], [c_427, c_26])).
% 20.31/10.71  tff(c_93575, plain, (![A_41951, D_41952, B_41953]: (r2_hidden(k1_funct_1(A_41951, D_41952), B_41953) | ~r2_hidden(D_41952, k1_relat_1(A_41951)) | ~v1_funct_1(A_41951) | ~v1_relat_1(A_41951) | ~r1_tarski(k2_relat_1(A_41951), B_41953))), inference(resolution, [status(thm)], [c_30, c_93512])).
% 20.31/10.71  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.31/10.71  tff(c_171, plain, (![D_99, B_100, A_101]: (D_99=B_100 | D_99=A_101 | ~r2_hidden(D_99, k2_tarski(A_101, B_100)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.31/10.71  tff(c_180, plain, (![D_99, A_8]: (D_99=A_8 | D_99=A_8 | ~r2_hidden(D_99, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_171])).
% 20.31/10.71  tff(c_93787, plain, (![A_42109, D_42110, A_42111]: (k1_funct_1(A_42109, D_42110)=A_42111 | ~r2_hidden(D_42110, k1_relat_1(A_42109)) | ~v1_funct_1(A_42109) | ~v1_relat_1(A_42109) | ~r1_tarski(k2_relat_1(A_42109), k1_tarski(A_42111)))), inference(resolution, [status(thm)], [c_93575, c_180])).
% 20.31/10.71  tff(c_93872, plain, (![D_42110, A_42111]: (k1_funct_1('#skF_10', D_42110)=A_42111 | ~r2_hidden(D_42110, '#skF_7') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r1_tarski(k2_relat_1('#skF_10'), k1_tarski(A_42111)))), inference(superposition, [status(thm), theory('equality')], [c_803, c_93787])).
% 20.31/10.71  tff(c_93894, plain, (![D_42267, A_42268]: (k1_funct_1('#skF_10', D_42267)=A_42268 | ~r2_hidden(D_42267, '#skF_7') | ~r1_tarski(k2_relat_1('#skF_10'), k1_tarski(A_42268)))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_84, c_93872])).
% 20.31/10.71  tff(c_94048, plain, (![A_42424]: (k1_funct_1('#skF_10', '#skF_9')=A_42424 | ~r1_tarski(k2_relat_1('#skF_10'), k1_tarski(A_42424)))), inference(resolution, [status(thm)], [c_78, c_93894])).
% 20.31/10.71  tff(c_94190, plain, (![A_42424]: (k1_funct_1('#skF_10', '#skF_9')=A_42424 | ~v5_relat_1('#skF_10', k1_tarski(A_42424)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_94048])).
% 20.31/10.71  tff(c_94195, plain, (![A_42580]: (k1_funct_1('#skF_10', '#skF_9')=A_42580 | ~v5_relat_1('#skF_10', k1_tarski(A_42580)))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_94190])).
% 20.31/10.71  tff(c_94332, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_211, c_94195])).
% 20.31/10.71  tff(c_94336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_94332])).
% 20.31/10.71  tff(c_94337, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_802])).
% 20.31/10.71  tff(c_95, plain, (![D_75, A_76]: (r2_hidden(D_75, k2_tarski(A_76, D_75)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.31/10.71  tff(c_98, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_95])).
% 20.31/10.71  tff(c_105, plain, (![B_80, A_81]: (~r1_tarski(B_80, A_81) | ~r2_hidden(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.31/10.71  tff(c_119, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_98, c_105])).
% 20.31/10.71  tff(c_94359, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_94337, c_119])).
% 20.31/10.71  tff(c_94369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_94359])).
% 20.31/10.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.31/10.71  
% 20.31/10.71  Inference rules
% 20.31/10.71  ----------------------
% 20.31/10.71  #Ref     : 0
% 20.31/10.71  #Sup     : 11174
% 20.31/10.71  #Fact    : 34
% 20.31/10.71  #Define  : 0
% 20.31/10.71  #Split   : 24
% 20.31/10.71  #Chain   : 0
% 20.31/10.71  #Close   : 0
% 20.31/10.71  
% 20.31/10.71  Ordering : KBO
% 20.31/10.71  
% 20.31/10.71  Simplification rules
% 20.31/10.71  ----------------------
% 20.31/10.71  #Subsume      : 606
% 20.31/10.71  #Demod        : 1708
% 20.31/10.71  #Tautology    : 309
% 20.31/10.71  #SimpNegUnit  : 11
% 20.31/10.71  #BackRed      : 14
% 20.31/10.71  
% 20.31/10.71  #Partial instantiations: 27240
% 20.31/10.71  #Strategies tried      : 1
% 20.31/10.71  
% 20.31/10.71  Timing (in seconds)
% 20.31/10.71  ----------------------
% 20.31/10.72  Preprocessing        : 0.35
% 20.31/10.72  Parsing              : 0.18
% 20.31/10.72  CNF conversion       : 0.03
% 20.31/10.72  Main loop            : 9.57
% 20.31/10.72  Inferencing          : 2.51
% 20.31/10.72  Reduction            : 3.12
% 20.31/10.72  Demodulation         : 2.36
% 20.31/10.72  BG Simplification    : 0.40
% 20.31/10.72  Subsumption          : 3.23
% 20.31/10.72  Abstraction          : 0.67
% 20.31/10.72  MUC search           : 0.00
% 20.31/10.72  Cooper               : 0.00
% 20.31/10.72  Total                : 9.96
% 20.31/10.72  Index Insertion      : 0.00
% 20.31/10.72  Index Deletion       : 0.00
% 20.31/10.72  Index Matching       : 0.00
% 20.31/10.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
