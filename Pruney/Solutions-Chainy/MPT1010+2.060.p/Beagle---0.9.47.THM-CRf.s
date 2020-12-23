%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   71 (  97 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 184 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_45,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_91,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_91])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_129,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_133,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_129])).

tff(c_326,plain,(
    ! [B_94,A_95,C_96] :
      ( k1_xboole_0 = B_94
      | k1_relset_1(A_95,B_94,C_96) = A_95
      | ~ v1_funct_2(C_96,A_95,B_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_333,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_326])).

tff(c_337,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_133,c_333])).

tff(c_338,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_106,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_110,plain,(
    k2_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_106])).

tff(c_227,plain,(
    ! [A_72,B_73,C_74] :
      ( m1_subset_1(k2_relset_1(A_72,B_73,C_74),k1_zfmisc_1(B_73))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_242,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_227])).

tff(c_247,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_242])).

tff(c_267,plain,(
    ! [B_78,A_79] :
      ( r2_hidden(k1_funct_1(B_78,A_79),k2_relat_1(B_78))
      | ~ r2_hidden(A_79,k1_relat_1(B_78))
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [C_13,A_10,B_11] :
      ( r2_hidden(C_13,A_10)
      | ~ r2_hidden(C_13,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_434,plain,(
    ! [B_117,A_118,A_119] :
      ( r2_hidden(k1_funct_1(B_117,A_118),A_119)
      | ~ m1_subset_1(k2_relat_1(B_117),k1_zfmisc_1(A_119))
      | ~ r2_hidden(A_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_267,c_20])).

tff(c_436,plain,(
    ! [A_118] :
      ( r2_hidden(k1_funct_1('#skF_6',A_118),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_118,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_247,c_434])).

tff(c_440,plain,(
    ! [A_120] :
      ( r2_hidden(k1_funct_1('#skF_6',A_120),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_120,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_338,c_436])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_452,plain,(
    ! [A_121] :
      ( k1_funct_1('#skF_6',A_121) = '#skF_4'
      | ~ r2_hidden(A_121,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_440,c_4])).

tff(c_467,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_452])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_467])).

tff(c_475,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    ! [B_38,A_39] :
      ( ~ r1_tarski(B_38,A_39)
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_502,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_79])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.87/1.46  
% 2.87/1.46  %Foreground sorts:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Background operators:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Foreground operators:
% 2.87/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.46  
% 3.00/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.48  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.00/1.48  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.48  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.00/1.48  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.00/1.48  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.00/1.48  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.00/1.48  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.00/1.48  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.00/1.48  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.00/1.48  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.00/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.48  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.48  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.48  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.48  tff(c_91, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.48  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_91])).
% 3.00/1.48  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.48  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.48  tff(c_129, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.48  tff(c_133, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_129])).
% 3.00/1.48  tff(c_326, plain, (![B_94, A_95, C_96]: (k1_xboole_0=B_94 | k1_relset_1(A_95, B_94, C_96)=A_95 | ~v1_funct_2(C_96, A_95, B_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.00/1.48  tff(c_333, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_326])).
% 3.00/1.48  tff(c_337, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_133, c_333])).
% 3.00/1.48  tff(c_338, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_337])).
% 3.00/1.48  tff(c_106, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.48  tff(c_110, plain, (k2_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_106])).
% 3.00/1.48  tff(c_227, plain, (![A_72, B_73, C_74]: (m1_subset_1(k2_relset_1(A_72, B_73, C_74), k1_zfmisc_1(B_73)) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.48  tff(c_242, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_110, c_227])).
% 3.00/1.48  tff(c_247, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_242])).
% 3.00/1.48  tff(c_267, plain, (![B_78, A_79]: (r2_hidden(k1_funct_1(B_78, A_79), k2_relat_1(B_78)) | ~r2_hidden(A_79, k1_relat_1(B_78)) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.48  tff(c_20, plain, (![C_13, A_10, B_11]: (r2_hidden(C_13, A_10) | ~r2_hidden(C_13, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.48  tff(c_434, plain, (![B_117, A_118, A_119]: (r2_hidden(k1_funct_1(B_117, A_118), A_119) | ~m1_subset_1(k2_relat_1(B_117), k1_zfmisc_1(A_119)) | ~r2_hidden(A_118, k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_267, c_20])).
% 3.00/1.48  tff(c_436, plain, (![A_118]: (r2_hidden(k1_funct_1('#skF_6', A_118), k1_tarski('#skF_4')) | ~r2_hidden(A_118, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_247, c_434])).
% 3.00/1.48  tff(c_440, plain, (![A_120]: (r2_hidden(k1_funct_1('#skF_6', A_120), k1_tarski('#skF_4')) | ~r2_hidden(A_120, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_338, c_436])).
% 3.00/1.48  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.48  tff(c_452, plain, (![A_121]: (k1_funct_1('#skF_6', A_121)='#skF_4' | ~r2_hidden(A_121, '#skF_3'))), inference(resolution, [status(thm)], [c_440, c_4])).
% 3.00/1.48  tff(c_467, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_452])).
% 3.00/1.48  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_467])).
% 3.00/1.48  tff(c_475, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_337])).
% 3.00/1.48  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.48  tff(c_72, plain, (![B_38, A_39]: (~r1_tarski(B_38, A_39) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.00/1.48  tff(c_79, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_72])).
% 3.00/1.48  tff(c_502, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_475, c_79])).
% 3.00/1.48  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_502])).
% 3.00/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.48  
% 3.00/1.48  Inference rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Ref     : 0
% 3.00/1.48  #Sup     : 101
% 3.00/1.48  #Fact    : 0
% 3.00/1.48  #Define  : 0
% 3.00/1.48  #Split   : 1
% 3.00/1.48  #Chain   : 0
% 3.00/1.48  #Close   : 0
% 3.00/1.48  
% 3.00/1.48  Ordering : KBO
% 3.00/1.48  
% 3.00/1.48  Simplification rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Subsume      : 6
% 3.00/1.48  #Demod        : 36
% 3.00/1.48  #Tautology    : 38
% 3.00/1.48  #SimpNegUnit  : 1
% 3.00/1.48  #BackRed      : 6
% 3.00/1.48  
% 3.00/1.48  #Partial instantiations: 0
% 3.00/1.48  #Strategies tried      : 1
% 3.00/1.48  
% 3.00/1.48  Timing (in seconds)
% 3.00/1.48  ----------------------
% 3.00/1.48  Preprocessing        : 0.32
% 3.00/1.48  Parsing              : 0.17
% 3.00/1.48  CNF conversion       : 0.02
% 3.00/1.48  Main loop            : 0.39
% 3.00/1.49  Inferencing          : 0.13
% 3.00/1.49  Reduction            : 0.12
% 3.00/1.49  Demodulation         : 0.09
% 3.00/1.49  BG Simplification    : 0.02
% 3.00/1.49  Subsumption          : 0.08
% 3.00/1.49  Abstraction          : 0.02
% 3.00/1.49  MUC search           : 0.00
% 3.00/1.49  Cooper               : 0.00
% 3.00/1.49  Total                : 0.74
% 3.00/1.49  Index Insertion      : 0.00
% 3.00/1.49  Index Deletion       : 0.00
% 3.00/1.49  Index Matching       : 0.00
% 3.00/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
