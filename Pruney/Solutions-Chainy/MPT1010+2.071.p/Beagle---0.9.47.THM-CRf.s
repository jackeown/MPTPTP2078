%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 101 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 189 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_84,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_115,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_119,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_115])).

tff(c_90,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_88,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_280,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_284,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_280])).

tff(c_570,plain,(
    ! [B_267,A_268,C_269] :
      ( k1_xboole_0 = B_267
      | k1_relset_1(A_268,B_267,C_269) = A_268
      | ~ v1_funct_2(C_269,A_268,B_267)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_268,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_573,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_570])).

tff(c_576,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_284,c_573])).

tff(c_577,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_404,plain,(
    ! [B_194,A_195] :
      ( r2_hidden(k4_tarski(B_194,k1_funct_1(A_195,B_194)),A_195)
      | ~ r2_hidden(B_194,k1_relat_1(A_195))
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    ! [C_28,A_25,B_26] :
      ( r2_hidden(C_28,A_25)
      | ~ r2_hidden(C_28,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_834,plain,(
    ! [B_338,A_339,A_340] :
      ( r2_hidden(k4_tarski(B_338,k1_funct_1(A_339,B_338)),A_340)
      | ~ m1_subset_1(A_339,k1_zfmisc_1(A_340))
      | ~ r2_hidden(B_338,k1_relat_1(A_339))
      | ~ v1_funct_1(A_339)
      | ~ v1_relat_1(A_339) ) ),
    inference(resolution,[status(thm)],[c_404,c_54])).

tff(c_14,plain,(
    ! [D_15,B_13,A_12,C_14] :
      ( D_15 = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,k1_tarski(D_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_899,plain,(
    ! [A_345,B_346,D_347,C_348] :
      ( k1_funct_1(A_345,B_346) = D_347
      | ~ m1_subset_1(A_345,k1_zfmisc_1(k2_zfmisc_1(C_348,k1_tarski(D_347))))
      | ~ r2_hidden(B_346,k1_relat_1(A_345))
      | ~ v1_funct_1(A_345)
      | ~ v1_relat_1(A_345) ) ),
    inference(resolution,[status(thm)],[c_834,c_14])).

tff(c_901,plain,(
    ! [B_346] :
      ( k1_funct_1('#skF_6',B_346) = '#skF_4'
      | ~ r2_hidden(B_346,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_86,c_899])).

tff(c_905,plain,(
    ! [B_349] :
      ( k1_funct_1('#skF_6',B_349) = '#skF_4'
      | ~ r2_hidden(B_349,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_90,c_577,c_901])).

tff(c_919,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_905])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_919])).

tff(c_927,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    ! [A_122,B_123,C_124,D_125] : k3_enumset1(A_122,A_122,B_123,C_124,D_125) = k2_enumset1(A_122,B_123,C_124,D_125) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [C_18,G_24,B_17,D_19,E_20] : r2_hidden(G_24,k3_enumset1(G_24,B_17,C_18,D_19,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_238,plain,(
    ! [A_127,B_128,C_129,D_130] : r2_hidden(A_127,k2_enumset1(A_127,B_128,C_129,D_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_28])).

tff(c_249,plain,(
    ! [A_131,B_132,C_133] : r2_hidden(A_131,k1_enumset1(A_131,B_132,C_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_238])).

tff(c_260,plain,(
    ! [A_134,B_135] : r2_hidden(A_134,k2_tarski(A_134,B_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_249])).

tff(c_271,plain,(
    ! [A_136] : r2_hidden(A_136,k1_tarski(A_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_260])).

tff(c_64,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_278,plain,(
    ! [A_136] : ~ r1_tarski(k1_tarski(A_136),A_136) ),
    inference(resolution,[status(thm)],[c_271,c_64])).

tff(c_941,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_278])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/2.15  
% 4.61/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/2.15  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.61/2.15  
% 4.61/2.15  %Foreground sorts:
% 4.61/2.15  
% 4.61/2.15  
% 4.61/2.15  %Background operators:
% 4.61/2.15  
% 4.61/2.15  
% 4.61/2.15  %Foreground operators:
% 4.61/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.61/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/2.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.61/2.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.61/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.61/2.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.61/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/2.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.61/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/2.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/2.15  tff('#skF_5', type, '#skF_5': $i).
% 4.61/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.61/2.15  tff('#skF_6', type, '#skF_6': $i).
% 4.61/2.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/2.15  tff('#skF_3', type, '#skF_3': $i).
% 4.61/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.61/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/2.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.61/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.61/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.61/2.15  tff('#skF_4', type, '#skF_4': $i).
% 4.61/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.61/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/2.15  
% 4.72/2.17  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.72/2.17  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.72/2.17  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.72/2.17  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.72/2.17  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.72/2.17  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 4.72/2.17  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.72/2.17  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 4.72/2.17  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.72/2.17  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.72/2.17  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.72/2.17  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.72/2.17  tff(f_62, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 4.72/2.17  tff(f_92, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.72/2.17  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.72/2.17  tff(c_82, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.72/2.17  tff(c_84, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.72/2.17  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.72/2.17  tff(c_115, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.72/2.17  tff(c_119, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_115])).
% 4.72/2.17  tff(c_90, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.72/2.17  tff(c_88, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.72/2.17  tff(c_280, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.72/2.17  tff(c_284, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_280])).
% 4.72/2.17  tff(c_570, plain, (![B_267, A_268, C_269]: (k1_xboole_0=B_267 | k1_relset_1(A_268, B_267, C_269)=A_268 | ~v1_funct_2(C_269, A_268, B_267) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.72/2.17  tff(c_573, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_570])).
% 4.72/2.17  tff(c_576, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_284, c_573])).
% 4.72/2.17  tff(c_577, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_576])).
% 4.72/2.17  tff(c_404, plain, (![B_194, A_195]: (r2_hidden(k4_tarski(B_194, k1_funct_1(A_195, B_194)), A_195) | ~r2_hidden(B_194, k1_relat_1(A_195)) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.72/2.17  tff(c_54, plain, (![C_28, A_25, B_26]: (r2_hidden(C_28, A_25) | ~r2_hidden(C_28, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/2.17  tff(c_834, plain, (![B_338, A_339, A_340]: (r2_hidden(k4_tarski(B_338, k1_funct_1(A_339, B_338)), A_340) | ~m1_subset_1(A_339, k1_zfmisc_1(A_340)) | ~r2_hidden(B_338, k1_relat_1(A_339)) | ~v1_funct_1(A_339) | ~v1_relat_1(A_339))), inference(resolution, [status(thm)], [c_404, c_54])).
% 4.72/2.17  tff(c_14, plain, (![D_15, B_13, A_12, C_14]: (D_15=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, k1_tarski(D_15))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.72/2.17  tff(c_899, plain, (![A_345, B_346, D_347, C_348]: (k1_funct_1(A_345, B_346)=D_347 | ~m1_subset_1(A_345, k1_zfmisc_1(k2_zfmisc_1(C_348, k1_tarski(D_347)))) | ~r2_hidden(B_346, k1_relat_1(A_345)) | ~v1_funct_1(A_345) | ~v1_relat_1(A_345))), inference(resolution, [status(thm)], [c_834, c_14])).
% 4.72/2.17  tff(c_901, plain, (![B_346]: (k1_funct_1('#skF_6', B_346)='#skF_4' | ~r2_hidden(B_346, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_86, c_899])).
% 4.72/2.17  tff(c_905, plain, (![B_349]: (k1_funct_1('#skF_6', B_349)='#skF_4' | ~r2_hidden(B_349, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_90, c_577, c_901])).
% 4.72/2.17  tff(c_919, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_84, c_905])).
% 4.72/2.17  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_919])).
% 4.72/2.17  tff(c_927, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_576])).
% 4.72/2.17  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.72/2.17  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/2.17  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.72/2.17  tff(c_198, plain, (![A_122, B_123, C_124, D_125]: (k3_enumset1(A_122, A_122, B_123, C_124, D_125)=k2_enumset1(A_122, B_123, C_124, D_125))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.72/2.17  tff(c_28, plain, (![C_18, G_24, B_17, D_19, E_20]: (r2_hidden(G_24, k3_enumset1(G_24, B_17, C_18, D_19, E_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.72/2.17  tff(c_238, plain, (![A_127, B_128, C_129, D_130]: (r2_hidden(A_127, k2_enumset1(A_127, B_128, C_129, D_130)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_28])).
% 4.72/2.17  tff(c_249, plain, (![A_131, B_132, C_133]: (r2_hidden(A_131, k1_enumset1(A_131, B_132, C_133)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_238])).
% 4.72/2.17  tff(c_260, plain, (![A_134, B_135]: (r2_hidden(A_134, k2_tarski(A_134, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_249])).
% 4.72/2.17  tff(c_271, plain, (![A_136]: (r2_hidden(A_136, k1_tarski(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_260])).
% 4.72/2.17  tff(c_64, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.72/2.17  tff(c_278, plain, (![A_136]: (~r1_tarski(k1_tarski(A_136), A_136))), inference(resolution, [status(thm)], [c_271, c_64])).
% 4.72/2.17  tff(c_941, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_927, c_278])).
% 4.72/2.17  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_941])).
% 4.72/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/2.17  
% 4.72/2.17  Inference rules
% 4.72/2.17  ----------------------
% 4.72/2.17  #Ref     : 0
% 4.72/2.17  #Sup     : 198
% 4.72/2.17  #Fact    : 0
% 4.72/2.17  #Define  : 0
% 4.72/2.17  #Split   : 3
% 4.72/2.17  #Chain   : 0
% 4.72/2.17  #Close   : 0
% 4.72/2.17  
% 4.72/2.17  Ordering : KBO
% 4.72/2.17  
% 4.72/2.17  Simplification rules
% 4.72/2.17  ----------------------
% 4.72/2.18  #Subsume      : 37
% 4.72/2.18  #Demod        : 35
% 4.72/2.18  #Tautology    : 44
% 4.72/2.18  #SimpNegUnit  : 1
% 4.72/2.18  #BackRed      : 4
% 4.72/2.18  
% 4.72/2.18  #Partial instantiations: 0
% 4.72/2.18  #Strategies tried      : 1
% 4.72/2.18  
% 4.72/2.18  Timing (in seconds)
% 4.72/2.18  ----------------------
% 4.72/2.18  Preprocessing        : 0.55
% 4.72/2.18  Parsing              : 0.26
% 4.72/2.18  CNF conversion       : 0.04
% 4.72/2.18  Main loop            : 0.74
% 4.72/2.18  Inferencing          : 0.26
% 4.72/2.18  Reduction            : 0.21
% 4.72/2.18  Demodulation         : 0.15
% 4.72/2.18  BG Simplification    : 0.04
% 4.72/2.18  Subsumption          : 0.16
% 4.72/2.18  Abstraction          : 0.05
% 4.72/2.18  MUC search           : 0.00
% 4.72/2.18  Cooper               : 0.00
% 4.72/2.18  Total                : 1.34
% 4.72/2.18  Index Insertion      : 0.00
% 4.72/2.18  Index Deletion       : 0.00
% 4.72/2.18  Index Matching       : 0.00
% 4.72/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
