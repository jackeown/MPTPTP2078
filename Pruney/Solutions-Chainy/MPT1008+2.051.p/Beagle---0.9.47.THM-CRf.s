%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:33 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 122 expanded)
%              Number of leaves         :   40 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 229 expanded)
%              Number of equality atoms :   49 (  84 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [D_39,A_40] : r2_hidden(D_39,k2_tarski(A_40,D_39)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_119,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_123,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = k1_xboole_0
      | k2_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_38])).

tff(c_128,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_129,plain,(
    ! [A_57] :
      ( k2_relat_1(A_57) = k1_xboole_0
      | k1_relat_1(A_57) != k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_129])).

tff(c_135,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_132])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( k1_tarski(k1_funct_1(B_20,A_19)) = k2_relat_1(B_20)
      | k1_tarski(A_19) != k1_relat_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_198,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_202,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_198])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_203,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_56])).

tff(c_237,plain,
    ( k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_203])).

tff(c_240,plain,(
    k1_tarski('#skF_3') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_64,c_237])).

tff(c_188,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_192,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_188])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_171,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(B_70) = A_71
      | k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_tarski(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_241,plain,(
    ! [B_83,B_84] :
      ( k1_tarski(B_83) = k1_relat_1(B_84)
      | k1_relat_1(B_84) = k1_xboole_0
      | ~ v4_relat_1(B_84,k1_tarski(B_83))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_36,c_171])).

tff(c_247,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_241])).

tff(c_250,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_240,c_250])).

tff(c_254,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_344,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_347,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_344])).

tff(c_349,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_347])).

tff(c_2746,plain,(
    ! [D_5048,C_5049,A_5050,B_5051] :
      ( r2_hidden(k1_funct_1(D_5048,C_5049),k2_relset_1(A_5050,B_5051,D_5048))
      | k1_xboole_0 = B_5051
      | ~ r2_hidden(C_5049,A_5050)
      | ~ m1_subset_1(D_5048,k1_zfmisc_1(k2_zfmisc_1(A_5050,B_5051)))
      | ~ v1_funct_2(D_5048,A_5050,B_5051)
      | ~ v1_funct_1(D_5048) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2758,plain,(
    ! [C_5049] :
      ( r2_hidden(k1_funct_1('#skF_5',C_5049),k1_xboole_0)
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_5049,k1_tarski('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')))
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_2746])).

tff(c_2761,plain,(
    ! [C_5049] :
      ( r2_hidden(k1_funct_1('#skF_5',C_5049),k1_xboole_0)
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_5049,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2758])).

tff(c_2763,plain,(
    ! [C_5130] :
      ( r2_hidden(k1_funct_1('#skF_5',C_5130),k1_xboole_0)
      | ~ r2_hidden(C_5130,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2761])).

tff(c_44,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2768,plain,(
    ! [C_5130] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_5',C_5130))
      | ~ r2_hidden(C_5130,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2763,c_44])).

tff(c_2776,plain,(
    ! [C_5209] : ~ r2_hidden(C_5209,k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2768])).

tff(c_2790,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_80,c_2776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:32:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.63  
% 3.80/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.80/1.63  
% 3.80/1.63  %Foreground sorts:
% 3.80/1.63  
% 3.80/1.63  
% 3.80/1.63  %Background operators:
% 3.80/1.63  
% 3.80/1.63  
% 3.80/1.63  %Foreground operators:
% 3.80/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.80/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.80/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.80/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.80/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.80/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.80/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.80/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.80/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.63  
% 3.80/1.64  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.80/1.64  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.80/1.64  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.80/1.64  tff(f_111, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.80/1.64  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.80/1.64  tff(f_60, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.80/1.64  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.80/1.64  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.64  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.80/1.64  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.80/1.64  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.80/1.64  tff(f_99, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.80/1.64  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.80/1.64  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.80/1.64  tff(c_77, plain, (![D_39, A_40]: (r2_hidden(D_39, k2_tarski(A_40, D_39)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.64  tff(c_80, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77])).
% 3.80/1.64  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.80/1.64  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.64  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.64  tff(c_62, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.64  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.64  tff(c_119, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.80/1.64  tff(c_123, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_119])).
% 3.80/1.64  tff(c_38, plain, (![A_18]: (k1_relat_1(A_18)=k1_xboole_0 | k2_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.80/1.64  tff(c_127, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_38])).
% 3.80/1.64  tff(c_128, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127])).
% 3.80/1.64  tff(c_129, plain, (![A_57]: (k2_relat_1(A_57)=k1_xboole_0 | k1_relat_1(A_57)!=k1_xboole_0 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.80/1.64  tff(c_132, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_129])).
% 3.80/1.64  tff(c_135, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_128, c_132])).
% 3.80/1.64  tff(c_42, plain, (![B_20, A_19]: (k1_tarski(k1_funct_1(B_20, A_19))=k2_relat_1(B_20) | k1_tarski(A_19)!=k1_relat_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.64  tff(c_198, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.80/1.64  tff(c_202, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_198])).
% 3.80/1.64  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.64  tff(c_203, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_56])).
% 3.80/1.64  tff(c_237, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_203])).
% 3.80/1.64  tff(c_240, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_64, c_237])).
% 3.80/1.64  tff(c_188, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.64  tff(c_192, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_188])).
% 3.80/1.64  tff(c_36, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.64  tff(c_171, plain, (![B_70, A_71]: (k1_tarski(B_70)=A_71 | k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_tarski(B_70)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.64  tff(c_241, plain, (![B_83, B_84]: (k1_tarski(B_83)=k1_relat_1(B_84) | k1_relat_1(B_84)=k1_xboole_0 | ~v4_relat_1(B_84, k1_tarski(B_83)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_36, c_171])).
% 3.80/1.64  tff(c_247, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_192, c_241])).
% 3.80/1.64  tff(c_250, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_247])).
% 3.80/1.64  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_240, c_250])).
% 3.80/1.64  tff(c_254, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_127])).
% 3.80/1.64  tff(c_344, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.80/1.64  tff(c_347, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_344])).
% 3.80/1.64  tff(c_349, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_254, c_347])).
% 3.80/1.64  tff(c_2746, plain, (![D_5048, C_5049, A_5050, B_5051]: (r2_hidden(k1_funct_1(D_5048, C_5049), k2_relset_1(A_5050, B_5051, D_5048)) | k1_xboole_0=B_5051 | ~r2_hidden(C_5049, A_5050) | ~m1_subset_1(D_5048, k1_zfmisc_1(k2_zfmisc_1(A_5050, B_5051))) | ~v1_funct_2(D_5048, A_5050, B_5051) | ~v1_funct_1(D_5048))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.80/1.64  tff(c_2758, plain, (![C_5049]: (r2_hidden(k1_funct_1('#skF_5', C_5049), k1_xboole_0) | k1_xboole_0='#skF_4' | ~r2_hidden(C_5049, k1_tarski('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))) | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_349, c_2746])).
% 3.80/1.64  tff(c_2761, plain, (![C_5049]: (r2_hidden(k1_funct_1('#skF_5', C_5049), k1_xboole_0) | k1_xboole_0='#skF_4' | ~r2_hidden(C_5049, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2758])).
% 3.80/1.64  tff(c_2763, plain, (![C_5130]: (r2_hidden(k1_funct_1('#skF_5', C_5130), k1_xboole_0) | ~r2_hidden(C_5130, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2761])).
% 3.80/1.64  tff(c_44, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.80/1.64  tff(c_2768, plain, (![C_5130]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_5', C_5130)) | ~r2_hidden(C_5130, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_2763, c_44])).
% 3.80/1.64  tff(c_2776, plain, (![C_5209]: (~r2_hidden(C_5209, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2768])).
% 3.80/1.64  tff(c_2790, plain, $false, inference(resolution, [status(thm)], [c_80, c_2776])).
% 3.80/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.64  
% 3.80/1.64  Inference rules
% 3.80/1.64  ----------------------
% 3.80/1.64  #Ref     : 0
% 3.80/1.64  #Sup     : 338
% 3.80/1.64  #Fact    : 4
% 3.80/1.64  #Define  : 0
% 3.80/1.64  #Split   : 2
% 3.80/1.64  #Chain   : 0
% 3.80/1.64  #Close   : 0
% 3.80/1.64  
% 3.80/1.64  Ordering : KBO
% 3.80/1.64  
% 3.80/1.64  Simplification rules
% 3.80/1.64  ----------------------
% 3.80/1.64  #Subsume      : 52
% 3.80/1.64  #Demod        : 87
% 3.80/1.64  #Tautology    : 115
% 3.80/1.64  #SimpNegUnit  : 15
% 3.80/1.64  #BackRed      : 2
% 3.80/1.64  
% 3.80/1.64  #Partial instantiations: 3120
% 3.80/1.64  #Strategies tried      : 1
% 3.80/1.64  
% 3.80/1.64  Timing (in seconds)
% 3.80/1.64  ----------------------
% 3.80/1.64  Preprocessing        : 0.33
% 3.80/1.64  Parsing              : 0.17
% 3.80/1.64  CNF conversion       : 0.02
% 3.80/1.64  Main loop            : 0.56
% 3.80/1.64  Inferencing          : 0.30
% 3.80/1.64  Reduction            : 0.13
% 3.80/1.64  Demodulation         : 0.09
% 3.80/1.65  BG Simplification    : 0.03
% 3.80/1.65  Subsumption          : 0.07
% 3.80/1.65  Abstraction          : 0.03
% 3.80/1.65  MUC search           : 0.00
% 3.80/1.65  Cooper               : 0.00
% 3.80/1.65  Total                : 0.92
% 3.80/1.65  Index Insertion      : 0.00
% 3.80/1.65  Index Deletion       : 0.00
% 3.80/1.65  Index Matching       : 0.00
% 3.80/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
