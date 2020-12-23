%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 949 expanded)
%              Number of leaves         :   25 ( 352 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 (3021 expanded)
%              Number of equality atoms :   52 (1009 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_66,axiom,(
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

tff(f_42,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38])).

tff(c_40,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_281,plain,(
    ! [B_63,C_64,A_65] :
      ( k1_xboole_0 = B_63
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_284,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_281])).

tff(c_293,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_284])).

tff(c_294,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_293])).

tff(c_166,plain,(
    ! [B_44,C_45,A_46] :
      ( k1_xboole_0 = B_44
      | v1_funct_2(C_45,A_46,B_44)
      | k1_relset_1(A_46,B_44,C_45) != A_46
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_166])).

tff(c_178,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_169])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_178])).

tff(c_22,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_11,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26])).

tff(c_54,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_52])).

tff(c_113,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_186,plain,(
    ~ m1_subset_1('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_113])).

tff(c_189,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_22])).

tff(c_188,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_18])).

tff(c_195,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_42])).

tff(c_207,plain,(
    m1_subset_1('#skF_5',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_195])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | v1_xboole_0(B_23)
      | ~ m1_subset_1(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_22,A_1] :
      ( A_22 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_22,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_111,plain,(
    ! [A_22,A_1] :
      ( A_22 = A_1
      | ~ m1_subset_1(A_22,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_108])).

tff(c_211,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_207,c_111])).

tff(c_212,plain,(
    m1_subset_1('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_207])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_212])).

tff(c_236,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11 ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_373,plain,(
    ! [A_71] :
      ( v1_funct_2('#skF_4',A_71,'#skF_4')
      | A_71 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_294,c_236])).

tff(c_306,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_22])).

tff(c_305,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_18])).

tff(c_317,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_42])).

tff(c_325,plain,(
    m1_subset_1('#skF_5',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_317])).

tff(c_348,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_325,c_111])).

tff(c_351,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_46])).

tff(c_377,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_373,c_351])).

tff(c_350,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_40])).

tff(c_378,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_350])).

tff(c_237,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_265,plain,(
    ! [C_58,B_59] :
      ( v1_funct_2(C_58,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,C_58) != k1_xboole_0
      | ~ m1_subset_1(C_58,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_47])).

tff(c_268,plain,(
    ! [B_59] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_237,c_265])).

tff(c_404,plain,(
    ! [B_74] :
      ( v1_funct_2('#skF_4','#skF_4',B_74)
      | k1_relset_1('#skF_4',B_74,'#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_294,c_294,c_294,c_268])).

tff(c_379,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_351])).

tff(c_407,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_404,c_379])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.11/1.29  
% 2.11/1.29  %Foreground sorts:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Background operators:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Foreground operators:
% 2.11/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.11/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.29  
% 2.40/1.31  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.40/1.31  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.40/1.31  tff(f_42, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.40/1.31  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.40/1.31  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.40/1.31  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.40/1.31  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.40/1.31  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.40/1.31  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.40/1.31  tff(c_38, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.40/1.31  tff(c_46, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38])).
% 2.40/1.31  tff(c_40, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.40/1.31  tff(c_281, plain, (![B_63, C_64, A_65]: (k1_xboole_0=B_63 | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.31  tff(c_284, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_42, c_281])).
% 2.40/1.31  tff(c_293, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_284])).
% 2.40/1.31  tff(c_294, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_293])).
% 2.40/1.31  tff(c_166, plain, (![B_44, C_45, A_46]: (k1_xboole_0=B_44 | v1_funct_2(C_45, A_46, B_44) | k1_relset_1(A_46, B_44, C_45)!=A_46 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_44))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.31  tff(c_169, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_42, c_166])).
% 2.40/1.31  tff(c_178, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_169])).
% 2.40/1.31  tff(c_179, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_178])).
% 2.40/1.31  tff(c_22, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.31  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.31  tff(c_26, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_11, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.31  tff(c_52, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26])).
% 2.40/1.31  tff(c_54, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_52])).
% 2.40/1.31  tff(c_113, plain, (~m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_54])).
% 2.40/1.31  tff(c_186, plain, (~m1_subset_1('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_113])).
% 2.40/1.31  tff(c_189, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_22])).
% 2.40/1.31  tff(c_188, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_18])).
% 2.40/1.31  tff(c_195, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_42])).
% 2.40/1.31  tff(c_207, plain, (m1_subset_1('#skF_5', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_195])).
% 2.40/1.31  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.31  tff(c_104, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | v1_xboole_0(B_23) | ~m1_subset_1(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.31  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.31  tff(c_108, plain, (![A_22, A_1]: (A_22=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_22, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_104, c_2])).
% 2.40/1.31  tff(c_111, plain, (![A_22, A_1]: (A_22=A_1 | ~m1_subset_1(A_22, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_108])).
% 2.40/1.31  tff(c_211, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_207, c_111])).
% 2.40/1.31  tff(c_212, plain, (m1_subset_1('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_207])).
% 2.40/1.31  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_212])).
% 2.40/1.31  tff(c_236, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11)), inference(splitRight, [status(thm)], [c_54])).
% 2.40/1.31  tff(c_373, plain, (![A_71]: (v1_funct_2('#skF_4', A_71, '#skF_4') | A_71='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_294, c_236])).
% 2.40/1.31  tff(c_306, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_22])).
% 2.40/1.31  tff(c_305, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_18])).
% 2.40/1.31  tff(c_317, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_42])).
% 2.40/1.31  tff(c_325, plain, (m1_subset_1('#skF_5', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_317])).
% 2.40/1.31  tff(c_348, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_325, c_111])).
% 2.40/1.31  tff(c_351, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_46])).
% 2.40/1.31  tff(c_377, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_373, c_351])).
% 2.40/1.31  tff(c_350, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_40])).
% 2.40/1.31  tff(c_378, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_350])).
% 2.40/1.31  tff(c_237, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_54])).
% 2.40/1.31  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.31  tff(c_30, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.31  tff(c_47, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 2.40/1.31  tff(c_265, plain, (![C_58, B_59]: (v1_funct_2(C_58, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, C_58)!=k1_xboole_0 | ~m1_subset_1(C_58, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_47])).
% 2.40/1.31  tff(c_268, plain, (![B_59]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_265])).
% 2.40/1.31  tff(c_404, plain, (![B_74]: (v1_funct_2('#skF_4', '#skF_4', B_74) | k1_relset_1('#skF_4', B_74, '#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_294, c_294, c_294, c_268])).
% 2.40/1.31  tff(c_379, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_351])).
% 2.40/1.31  tff(c_407, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_404, c_379])).
% 2.40/1.31  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_407])).
% 2.40/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  Inference rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Ref     : 0
% 2.40/1.31  #Sup     : 76
% 2.40/1.31  #Fact    : 0
% 2.40/1.31  #Define  : 0
% 2.40/1.31  #Split   : 1
% 2.40/1.31  #Chain   : 0
% 2.40/1.31  #Close   : 0
% 2.40/1.31  
% 2.40/1.31  Ordering : KBO
% 2.40/1.31  
% 2.40/1.31  Simplification rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Subsume      : 4
% 2.40/1.31  #Demod        : 88
% 2.40/1.31  #Tautology    : 59
% 2.40/1.31  #SimpNegUnit  : 5
% 2.40/1.31  #BackRed      : 31
% 2.40/1.31  
% 2.40/1.31  #Partial instantiations: 0
% 2.40/1.31  #Strategies tried      : 1
% 2.40/1.31  
% 2.40/1.31  Timing (in seconds)
% 2.40/1.31  ----------------------
% 2.40/1.31  Preprocessing        : 0.30
% 2.40/1.31  Parsing              : 0.15
% 2.40/1.31  CNF conversion       : 0.02
% 2.40/1.31  Main loop            : 0.25
% 2.40/1.31  Inferencing          : 0.09
% 2.40/1.31  Reduction            : 0.08
% 2.40/1.31  Demodulation         : 0.05
% 2.40/1.31  BG Simplification    : 0.02
% 2.40/1.31  Subsumption          : 0.05
% 2.40/1.31  Abstraction          : 0.02
% 2.40/1.31  MUC search           : 0.00
% 2.40/1.31  Cooper               : 0.00
% 2.40/1.31  Total                : 0.58
% 2.40/1.31  Index Insertion      : 0.00
% 2.40/1.31  Index Deletion       : 0.00
% 2.40/1.31  Index Matching       : 0.00
% 2.40/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
