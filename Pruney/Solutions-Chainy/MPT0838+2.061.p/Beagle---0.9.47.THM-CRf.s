%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:17 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 138 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 270 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_44,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_55,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_58])).

tff(c_63,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) = k1_xboole_0
      | k2_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_63])).

tff(c_72,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_150,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_159,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [A_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_86,B_87),B_88)
      | ~ r1_tarski(A_86,B_88)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    ! [A_98,B_99,B_100] :
      ( m1_subset_1('#skF_1'(A_98,B_99),B_100)
      | ~ r1_tarski(A_98,B_100)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_190,c_18])).

tff(c_212,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_221,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_84,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_42,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_95,plain,(
    ! [B_56] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_56),'#skF_5')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_56) ) ),
    inference(resolution,[status(thm)],[c_84,c_42])).

tff(c_222,plain,(
    ! [B_56] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_6'),B_56),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_221,c_95])).

tff(c_281,plain,(
    ! [B_99] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_99) ) ),
    inference(resolution,[status(thm)],[c_256,c_222])).

tff(c_319,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_322,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_319])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_159,c_322])).

tff(c_327,plain,(
    ! [B_99] : r1_tarski(k2_relat_1('#skF_6'),B_99) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_286,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_2'(A_101,B_102),B_102)
      | r2_hidden('#skF_3'(A_101,B_102),A_101)
      | B_102 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_598,plain,(
    ! [B_135,A_136] :
      ( ~ r1_tarski(B_135,'#skF_2'(A_136,B_135))
      | r2_hidden('#skF_3'(A_136,B_135),A_136)
      | B_135 = A_136 ) ),
    inference(resolution,[status(thm)],[c_286,c_32])).

tff(c_619,plain,(
    ! [A_137] :
      ( r2_hidden('#skF_3'(A_137,k1_xboole_0),A_137)
      | k1_xboole_0 = A_137 ) ),
    inference(resolution,[status(thm)],[c_16,c_598])).

tff(c_698,plain,(
    ! [A_140] :
      ( ~ r1_tarski(A_140,'#skF_3'(A_140,k1_xboole_0))
      | k1_xboole_0 = A_140 ) ),
    inference(resolution,[status(thm)],[c_619,c_32])).

tff(c_710,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_327,c_698])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_710])).

tff(c_725,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1091,plain,(
    ! [A_202,B_203,C_204] :
      ( k1_relset_1(A_202,B_203,C_204) = k1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1102,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1091])).

tff(c_1106,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_1102])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.00/1.46  
% 3.00/1.46  %Foreground sorts:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Background operators:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Foreground operators:
% 3.00/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.00/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.00/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.00/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.46  
% 3.00/1.47  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.00/1.47  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.00/1.47  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.00/1.47  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.00/1.47  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.00/1.47  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.00/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.00/1.47  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.00/1.47  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.00/1.47  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.47  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.00/1.47  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.00/1.47  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.00/1.47  tff(c_44, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.00/1.47  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.47  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.00/1.47  tff(c_55, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.00/1.47  tff(c_58, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_55])).
% 3.00/1.47  tff(c_61, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_58])).
% 3.00/1.47  tff(c_63, plain, (![A_53]: (k1_relat_1(A_53)=k1_xboole_0 | k2_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.47  tff(c_70, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_63])).
% 3.00/1.47  tff(c_72, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 3.00/1.47  tff(c_150, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.47  tff(c_159, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_150])).
% 3.00/1.47  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.00/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.47  tff(c_126, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.47  tff(c_190, plain, (![A_86, B_87, B_88]: (r2_hidden('#skF_1'(A_86, B_87), B_88) | ~r1_tarski(A_86, B_88) | r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_6, c_126])).
% 3.00/1.47  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.47  tff(c_256, plain, (![A_98, B_99, B_100]: (m1_subset_1('#skF_1'(A_98, B_99), B_100) | ~r1_tarski(A_98, B_100) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_190, c_18])).
% 3.00/1.47  tff(c_212, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.47  tff(c_221, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_212])).
% 3.00/1.47  tff(c_84, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.47  tff(c_42, plain, (![D_42]: (~r2_hidden(D_42, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_42, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.00/1.47  tff(c_95, plain, (![B_56]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_56), '#skF_5') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_56))), inference(resolution, [status(thm)], [c_84, c_42])).
% 3.00/1.47  tff(c_222, plain, (![B_56]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_6'), B_56), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_56))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_221, c_95])).
% 3.00/1.47  tff(c_281, plain, (![B_99]: (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_99))), inference(resolution, [status(thm)], [c_256, c_222])).
% 3.00/1.47  tff(c_319, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_281])).
% 3.00/1.47  tff(c_322, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_319])).
% 3.00/1.47  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_159, c_322])).
% 3.00/1.47  tff(c_327, plain, (![B_99]: (r1_tarski(k2_relat_1('#skF_6'), B_99))), inference(splitRight, [status(thm)], [c_281])).
% 3.00/1.47  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.47  tff(c_286, plain, (![A_101, B_102]: (r2_hidden('#skF_2'(A_101, B_102), B_102) | r2_hidden('#skF_3'(A_101, B_102), A_101) | B_102=A_101)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.00/1.47  tff(c_32, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.47  tff(c_598, plain, (![B_135, A_136]: (~r1_tarski(B_135, '#skF_2'(A_136, B_135)) | r2_hidden('#skF_3'(A_136, B_135), A_136) | B_135=A_136)), inference(resolution, [status(thm)], [c_286, c_32])).
% 3.00/1.47  tff(c_619, plain, (![A_137]: (r2_hidden('#skF_3'(A_137, k1_xboole_0), A_137) | k1_xboole_0=A_137)), inference(resolution, [status(thm)], [c_16, c_598])).
% 3.00/1.47  tff(c_698, plain, (![A_140]: (~r1_tarski(A_140, '#skF_3'(A_140, k1_xboole_0)) | k1_xboole_0=A_140)), inference(resolution, [status(thm)], [c_619, c_32])).
% 3.00/1.47  tff(c_710, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_327, c_698])).
% 3.00/1.47  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_710])).
% 3.00/1.47  tff(c_725, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 3.00/1.47  tff(c_1091, plain, (![A_202, B_203, C_204]: (k1_relset_1(A_202, B_203, C_204)=k1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.47  tff(c_1102, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1091])).
% 3.00/1.47  tff(c_1106, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_725, c_1102])).
% 3.00/1.47  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1106])).
% 3.00/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.47  
% 3.00/1.47  Inference rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Ref     : 0
% 3.00/1.47  #Sup     : 209
% 3.00/1.47  #Fact    : 0
% 3.00/1.47  #Define  : 0
% 3.00/1.47  #Split   : 4
% 3.00/1.47  #Chain   : 0
% 3.00/1.47  #Close   : 0
% 3.00/1.47  
% 3.00/1.47  Ordering : KBO
% 3.00/1.47  
% 3.00/1.47  Simplification rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Subsume      : 23
% 3.00/1.47  #Demod        : 70
% 3.00/1.47  #Tautology    : 59
% 3.00/1.47  #SimpNegUnit  : 4
% 3.00/1.47  #BackRed      : 3
% 3.00/1.47  
% 3.00/1.47  #Partial instantiations: 0
% 3.00/1.47  #Strategies tried      : 1
% 3.00/1.47  
% 3.00/1.47  Timing (in seconds)
% 3.00/1.47  ----------------------
% 3.00/1.47  Preprocessing        : 0.32
% 3.00/1.47  Parsing              : 0.17
% 3.00/1.47  CNF conversion       : 0.02
% 3.00/1.47  Main loop            : 0.40
% 3.00/1.47  Inferencing          : 0.16
% 3.00/1.47  Reduction            : 0.11
% 3.00/1.47  Demodulation         : 0.07
% 3.00/1.47  BG Simplification    : 0.02
% 3.00/1.47  Subsumption          : 0.07
% 3.00/1.47  Abstraction          : 0.02
% 3.00/1.47  MUC search           : 0.00
% 3.00/1.47  Cooper               : 0.00
% 3.00/1.47  Total                : 0.75
% 3.00/1.47  Index Insertion      : 0.00
% 3.00/1.47  Index Deletion       : 0.00
% 3.00/1.47  Index Matching       : 0.00
% 3.00/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
