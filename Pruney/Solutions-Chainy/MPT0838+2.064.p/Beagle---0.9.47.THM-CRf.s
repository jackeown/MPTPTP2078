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
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 135 expanded)
%              Number of leaves         :   41 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 250 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_56,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_107,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_117,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_122,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_117])).

tff(c_42,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) = k1_xboole_0
      | k2_relat_1(A_37) != k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_126,plain,
    ( k1_relat_1('#skF_8') = k1_xboole_0
    | k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_42])).

tff(c_127,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_167,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_181,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_167])).

tff(c_38,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v5_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_22] : k3_tarski(k1_zfmisc_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_235,plain,(
    ! [C_97,A_98,D_99] :
      ( r2_hidden(C_97,k3_tarski(A_98))
      | ~ r2_hidden(D_99,A_98)
      | ~ r2_hidden(C_97,D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_660,plain,(
    ! [C_161,B_162,A_163] :
      ( r2_hidden(C_161,k3_tarski(B_162))
      | ~ r2_hidden(C_161,A_163)
      | v1_xboole_0(B_162)
      | ~ m1_subset_1(A_163,B_162) ) ),
    inference(resolution,[status(thm)],[c_28,c_235])).

tff(c_701,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166),k3_tarski(B_167))
      | v1_xboole_0(B_167)
      | ~ m1_subset_1(A_166,B_167)
      | k1_xboole_0 = A_166 ) ),
    inference(resolution,[status(thm)],[c_2,c_660])).

tff(c_711,plain,(
    ! [A_166,A_22] :
      ( r2_hidden('#skF_1'(A_166),A_22)
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ m1_subset_1(A_166,k1_zfmisc_1(A_22))
      | k1_xboole_0 = A_166 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_701])).

tff(c_716,plain,(
    ! [A_168,A_169] :
      ( r2_hidden('#skF_1'(A_168),A_169)
      | ~ m1_subset_1(A_168,k1_zfmisc_1(A_169))
      | k1_xboole_0 = A_168 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_711])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_742,plain,(
    ! [A_170,A_171] :
      ( m1_subset_1('#skF_1'(A_170),A_171)
      | ~ m1_subset_1(A_170,k1_zfmisc_1(A_171))
      | k1_xboole_0 = A_170 ) ),
    inference(resolution,[status(thm)],[c_716,c_26])).

tff(c_473,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_493,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_473])).

tff(c_80,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k2_relset_1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1(D_66,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_85,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7')
    | k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_128,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_496,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_128])).

tff(c_749,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_742,c_496])).

tff(c_777,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_749])).

tff(c_787,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_777])).

tff(c_790,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_787])).

tff(c_794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_181,c_790])).

tff(c_795,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1036,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_relset_1(A_216,B_217,C_218) = k2_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1047,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_1036])).

tff(c_1051,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_1047])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_1051])).

tff(c_1054,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1373,plain,(
    ! [A_273,B_274,C_275] :
      ( k1_relset_1(A_273,B_274,C_275) = k1_relat_1(C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1388,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_1373])).

tff(c_1394,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_1388])).

tff(c_1396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.65  
% 3.14/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.65  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 3.14/1.65  
% 3.14/1.65  %Foreground sorts:
% 3.14/1.65  
% 3.14/1.65  
% 3.14/1.65  %Background operators:
% 3.14/1.65  
% 3.14/1.65  
% 3.14/1.65  %Foreground operators:
% 3.14/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.14/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.14/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.14/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.65  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.14/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.14/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.14/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.14/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.14/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.65  
% 3.14/1.67  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.14/1.67  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.14/1.67  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.14/1.67  tff(f_83, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.14/1.67  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.14/1.67  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.14/1.67  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.14/1.67  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.14/1.67  tff(f_45, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.14/1.67  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.14/1.67  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.14/1.67  tff(f_43, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 3.14/1.67  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.14/1.67  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.14/1.67  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.14/1.67  tff(c_56, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.67  tff(c_40, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.14/1.67  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.67  tff(c_107, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.14/1.67  tff(c_117, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_107])).
% 3.14/1.67  tff(c_122, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_117])).
% 3.14/1.67  tff(c_42, plain, (![A_37]: (k1_relat_1(A_37)=k1_xboole_0 | k2_relat_1(A_37)!=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.67  tff(c_126, plain, (k1_relat_1('#skF_8')=k1_xboole_0 | k2_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_42])).
% 3.14/1.67  tff(c_127, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 3.14/1.67  tff(c_167, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.67  tff(c_181, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_167])).
% 3.14/1.67  tff(c_38, plain, (![B_34, A_33]: (r1_tarski(k2_relat_1(B_34), A_33) | ~v5_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.67  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.67  tff(c_24, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.67  tff(c_22, plain, (![A_22]: (k3_tarski(k1_zfmisc_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.67  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.67  tff(c_28, plain, (![A_26, B_27]: (r2_hidden(A_26, B_27) | v1_xboole_0(B_27) | ~m1_subset_1(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.14/1.67  tff(c_235, plain, (![C_97, A_98, D_99]: (r2_hidden(C_97, k3_tarski(A_98)) | ~r2_hidden(D_99, A_98) | ~r2_hidden(C_97, D_99))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.67  tff(c_660, plain, (![C_161, B_162, A_163]: (r2_hidden(C_161, k3_tarski(B_162)) | ~r2_hidden(C_161, A_163) | v1_xboole_0(B_162) | ~m1_subset_1(A_163, B_162))), inference(resolution, [status(thm)], [c_28, c_235])).
% 3.14/1.67  tff(c_701, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166), k3_tarski(B_167)) | v1_xboole_0(B_167) | ~m1_subset_1(A_166, B_167) | k1_xboole_0=A_166)), inference(resolution, [status(thm)], [c_2, c_660])).
% 3.14/1.67  tff(c_711, plain, (![A_166, A_22]: (r2_hidden('#skF_1'(A_166), A_22) | v1_xboole_0(k1_zfmisc_1(A_22)) | ~m1_subset_1(A_166, k1_zfmisc_1(A_22)) | k1_xboole_0=A_166)), inference(superposition, [status(thm), theory('equality')], [c_22, c_701])).
% 3.14/1.67  tff(c_716, plain, (![A_168, A_169]: (r2_hidden('#skF_1'(A_168), A_169) | ~m1_subset_1(A_168, k1_zfmisc_1(A_169)) | k1_xboole_0=A_168)), inference(negUnitSimplification, [status(thm)], [c_24, c_711])).
% 3.14/1.67  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.67  tff(c_742, plain, (![A_170, A_171]: (m1_subset_1('#skF_1'(A_170), A_171) | ~m1_subset_1(A_170, k1_zfmisc_1(A_171)) | k1_xboole_0=A_170)), inference(resolution, [status(thm)], [c_716, c_26])).
% 3.14/1.67  tff(c_473, plain, (![A_137, B_138, C_139]: (k2_relset_1(A_137, B_138, C_139)=k2_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.14/1.67  tff(c_493, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_473])).
% 3.14/1.67  tff(c_80, plain, (![D_66]: (~r2_hidden(D_66, k2_relset_1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1(D_66, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.14/1.67  tff(c_85, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_80])).
% 3.14/1.67  tff(c_128, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_85])).
% 3.14/1.67  tff(c_496, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_128])).
% 3.14/1.67  tff(c_749, plain, (~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_742, c_496])).
% 3.14/1.67  tff(c_777, plain, (~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_127, c_749])).
% 3.14/1.67  tff(c_787, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_32, c_777])).
% 3.14/1.67  tff(c_790, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_787])).
% 3.14/1.67  tff(c_794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_181, c_790])).
% 3.14/1.67  tff(c_795, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_85])).
% 3.14/1.67  tff(c_1036, plain, (![A_216, B_217, C_218]: (k2_relset_1(A_216, B_217, C_218)=k2_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.14/1.67  tff(c_1047, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_1036])).
% 3.14/1.67  tff(c_1051, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_795, c_1047])).
% 3.14/1.67  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_1051])).
% 3.14/1.67  tff(c_1054, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 3.14/1.67  tff(c_1373, plain, (![A_273, B_274, C_275]: (k1_relset_1(A_273, B_274, C_275)=k1_relat_1(C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.14/1.67  tff(c_1388, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_1373])).
% 3.14/1.67  tff(c_1394, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_1388])).
% 3.14/1.67  tff(c_1396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1394])).
% 3.14/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.67  
% 3.14/1.67  Inference rules
% 3.14/1.67  ----------------------
% 3.14/1.67  #Ref     : 0
% 3.14/1.67  #Sup     : 273
% 3.14/1.67  #Fact    : 0
% 3.14/1.67  #Define  : 0
% 3.14/1.67  #Split   : 9
% 3.14/1.67  #Chain   : 0
% 3.14/1.67  #Close   : 0
% 3.14/1.67  
% 3.14/1.67  Ordering : KBO
% 3.14/1.67  
% 3.14/1.67  Simplification rules
% 3.14/1.67  ----------------------
% 3.14/1.67  #Subsume      : 20
% 3.14/1.67  #Demod        : 81
% 3.14/1.67  #Tautology    : 43
% 3.14/1.67  #SimpNegUnit  : 8
% 3.14/1.67  #BackRed      : 6
% 3.14/1.67  
% 3.14/1.67  #Partial instantiations: 0
% 3.14/1.67  #Strategies tried      : 1
% 3.14/1.67  
% 3.14/1.67  Timing (in seconds)
% 3.14/1.67  ----------------------
% 3.14/1.67  Preprocessing        : 0.33
% 3.14/1.67  Parsing              : 0.17
% 3.14/1.67  CNF conversion       : 0.03
% 3.14/1.67  Main loop            : 0.45
% 3.14/1.67  Inferencing          : 0.17
% 3.14/1.67  Reduction            : 0.12
% 3.14/1.67  Demodulation         : 0.08
% 3.14/1.67  BG Simplification    : 0.03
% 3.14/1.67  Subsumption          : 0.08
% 3.14/1.67  Abstraction          : 0.03
% 3.14/1.67  MUC search           : 0.00
% 3.14/1.67  Cooper               : 0.00
% 3.14/1.67  Total                : 0.81
% 3.14/1.67  Index Insertion      : 0.00
% 3.14/1.67  Index Deletion       : 0.00
% 3.14/1.67  Index Matching       : 0.00
% 3.14/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
