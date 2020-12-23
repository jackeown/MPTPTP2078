%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:24 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 185 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 379 expanded)
%              Number of equality atoms :   43 ( 123 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_136,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_24,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_24])).

tff(c_157,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1('#skF_1'(A_7,B_8),A_7)
      | k1_xboole_0 = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | k1_xboole_0 = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_179,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_188,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_179])).

tff(c_34,plain,(
    ! [D_35] :
      ( ~ r2_hidden(D_35,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_209,plain,(
    ! [D_65] :
      ( ~ r2_hidden(D_65,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_65,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_34])).

tff(c_213,plain,(
    ! [A_7] :
      ( ~ m1_subset_1('#skF_1'(A_7,k1_relat_1('#skF_4')),'#skF_3')
      | k1_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_16,c_209])).

tff(c_217,plain,(
    ! [A_66] :
      ( ~ m1_subset_1('#skF_1'(A_66,k1_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_213])).

tff(c_221,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_217])).

tff(c_224,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_221])).

tff(c_227,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k1_relset_1(A_67,B_68,C_69),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_242,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_227])).

tff(c_247,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_242])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_247])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_22,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_147,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_22])).

tff(c_149,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_252,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_149])).

tff(c_20,plain,(
    ! [A_10] :
      ( v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [A_38] :
      ( v1_xboole_0(k2_relat_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_40] :
      ( k2_relat_1(A_40) = k1_xboole_0
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_62,plain,(
    ! [A_41] :
      ( k2_relat_1(k2_relat_1(A_41)) = k1_xboole_0
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_71,plain,(
    ! [A_41] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_83,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_90,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(resolution,[status(thm)],[c_20,c_83])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [B_45,A_46] :
      ( ~ r1_xboole_0(B_45,A_46)
      | ~ r1_tarski(B_45,A_46)
      | v1_xboole_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_94,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_97,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_97])).

tff(c_111,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_50,plain,(
    ! [A_38] :
      ( k2_relat_1(A_38) = k1_xboole_0
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_118,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_50])).

tff(c_253,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_250,c_118])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_253])).

tff(c_286,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_296,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_36])).

tff(c_287,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_303,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_287])).

tff(c_441,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_448,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_441])).

tff(c_451,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_448])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.43/1.39  
% 2.43/1.39  %Foreground sorts:
% 2.43/1.39  
% 2.43/1.39  
% 2.43/1.39  %Background operators:
% 2.43/1.39  
% 2.43/1.39  
% 2.43/1.39  %Foreground operators:
% 2.43/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.43/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.43/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.43/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.39  
% 2.43/1.40  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.43/1.40  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.43/1.40  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.43/1.40  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.43/1.40  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.43/1.40  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.43/1.40  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.43/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.43/1.40  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.40  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.43/1.40  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.43/1.40  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.43/1.40  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.43/1.40  tff(c_136, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.43/1.40  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_136])).
% 2.43/1.40  tff(c_24, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.40  tff(c_148, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_140, c_24])).
% 2.43/1.40  tff(c_157, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_148])).
% 2.43/1.40  tff(c_18, plain, (![A_7, B_8]: (m1_subset_1('#skF_1'(A_7, B_8), A_7) | k1_xboole_0=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.40  tff(c_16, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | k1_xboole_0=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.40  tff(c_179, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.40  tff(c_188, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_179])).
% 2.43/1.40  tff(c_34, plain, (![D_35]: (~r2_hidden(D_35, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.43/1.40  tff(c_209, plain, (![D_65]: (~r2_hidden(D_65, k1_relat_1('#skF_4')) | ~m1_subset_1(D_65, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_34])).
% 2.43/1.40  tff(c_213, plain, (![A_7]: (~m1_subset_1('#skF_1'(A_7, k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_16, c_209])).
% 2.43/1.40  tff(c_217, plain, (![A_66]: (~m1_subset_1('#skF_1'(A_66, k1_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_66)))), inference(negUnitSimplification, [status(thm)], [c_157, c_213])).
% 2.43/1.40  tff(c_221, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_217])).
% 2.43/1.40  tff(c_224, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_157, c_221])).
% 2.43/1.40  tff(c_227, plain, (![A_67, B_68, C_69]: (m1_subset_1(k1_relset_1(A_67, B_68, C_69), k1_zfmisc_1(A_67)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.43/1.40  tff(c_242, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_227])).
% 2.43/1.40  tff(c_247, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_242])).
% 2.43/1.40  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_247])).
% 2.43/1.40  tff(c_250, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_148])).
% 2.43/1.40  tff(c_22, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.40  tff(c_147, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_140, c_22])).
% 2.43/1.40  tff(c_149, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_147])).
% 2.43/1.40  tff(c_252, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_149])).
% 2.43/1.40  tff(c_20, plain, (![A_10]: (v1_xboole_0(k2_relat_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.43/1.40  tff(c_46, plain, (![A_38]: (v1_xboole_0(k2_relat_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.43/1.40  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.40  tff(c_57, plain, (![A_40]: (k2_relat_1(A_40)=k1_xboole_0 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_46, c_2])).
% 2.43/1.40  tff(c_62, plain, (![A_41]: (k2_relat_1(k2_relat_1(A_41))=k1_xboole_0 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_20, c_57])).
% 2.43/1.40  tff(c_71, plain, (![A_41]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_41)) | ~v1_xboole_0(A_41))), inference(superposition, [status(thm), theory('equality')], [c_62, c_20])).
% 2.43/1.40  tff(c_83, plain, (![A_44]: (~v1_xboole_0(k2_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(splitLeft, [status(thm)], [c_71])).
% 2.43/1.40  tff(c_90, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_20, c_83])).
% 2.43/1.40  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.40  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.43/1.40  tff(c_91, plain, (![B_45, A_46]: (~r1_xboole_0(B_45, A_46) | ~r1_tarski(B_45, A_46) | v1_xboole_0(B_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.43/1.40  tff(c_94, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_91])).
% 2.43/1.40  tff(c_97, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_94])).
% 2.43/1.40  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_97])).
% 2.43/1.40  tff(c_111, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_71])).
% 2.43/1.40  tff(c_50, plain, (![A_38]: (k2_relat_1(A_38)=k1_xboole_0 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_46, c_2])).
% 2.43/1.40  tff(c_118, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_50])).
% 2.43/1.40  tff(c_253, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_250, c_118])).
% 2.43/1.40  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_253])).
% 2.43/1.40  tff(c_286, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_147])).
% 2.43/1.40  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.43/1.40  tff(c_296, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_36])).
% 2.43/1.40  tff(c_287, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_147])).
% 2.43/1.40  tff(c_303, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_287])).
% 2.43/1.40  tff(c_441, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.43/1.40  tff(c_448, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_441])).
% 2.43/1.40  tff(c_451, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_448])).
% 2.43/1.40  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_296, c_451])).
% 2.43/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.40  
% 2.43/1.40  Inference rules
% 2.43/1.40  ----------------------
% 2.43/1.40  #Ref     : 0
% 2.43/1.40  #Sup     : 76
% 2.43/1.40  #Fact    : 0
% 2.43/1.40  #Define  : 0
% 2.43/1.40  #Split   : 4
% 2.43/1.40  #Chain   : 0
% 2.43/1.40  #Close   : 0
% 2.43/1.40  
% 2.43/1.40  Ordering : KBO
% 2.43/1.40  
% 2.43/1.40  Simplification rules
% 2.43/1.40  ----------------------
% 2.43/1.40  #Subsume      : 13
% 2.43/1.40  #Demod        : 75
% 2.43/1.40  #Tautology    : 46
% 2.43/1.40  #SimpNegUnit  : 11
% 2.43/1.40  #BackRed      : 26
% 2.43/1.40  
% 2.43/1.40  #Partial instantiations: 0
% 2.43/1.40  #Strategies tried      : 1
% 2.43/1.40  
% 2.43/1.40  Timing (in seconds)
% 2.43/1.40  ----------------------
% 2.43/1.41  Preprocessing        : 0.32
% 2.43/1.41  Parsing              : 0.18
% 2.43/1.41  CNF conversion       : 0.02
% 2.43/1.41  Main loop            : 0.24
% 2.43/1.41  Inferencing          : 0.09
% 2.43/1.41  Reduction            : 0.07
% 2.43/1.41  Demodulation         : 0.05
% 2.43/1.41  BG Simplification    : 0.02
% 2.43/1.41  Subsumption          : 0.05
% 2.43/1.41  Abstraction          : 0.02
% 2.43/1.41  MUC search           : 0.00
% 2.43/1.41  Cooper               : 0.00
% 2.43/1.41  Total                : 0.60
% 2.43/1.41  Index Insertion      : 0.00
% 2.43/1.41  Index Deletion       : 0.00
% 2.43/1.41  Index Matching       : 0.00
% 2.43/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
