%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:10 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 125 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 240 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_95,negated_conjecture,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_32,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_47,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) = k1_xboole_0
      | k1_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_18])).

tff(c_67,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,(
    ! [A_46] :
      ( k1_relat_1(A_46) = k1_xboole_0
      | k2_relat_1(A_46) != k1_xboole_0
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_68])).

tff(c_74,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_71])).

tff(c_133,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_147,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69),B_70)
      | ~ r1_tarski(A_69,B_70)
      | k1_xboole_0 = A_69 ) ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_161,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1('#skF_2'(A_69),B_70)
      | ~ r1_tarski(A_69,B_70)
      | k1_xboole_0 = A_69 ) ),
    inference(resolution,[status(thm)],[c_149,c_10])).

tff(c_230,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_254,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_230])).

tff(c_57,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_98,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_256,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_98])).

tff(c_264,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_256])).

tff(c_267,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_264])).

tff(c_270,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_267])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_147,c_270])).

tff(c_275,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_486,plain,(
    ! [A_118,B_119,C_120] :
      ( k2_relset_1(A_118,B_119,C_120) = k2_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_505,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_486])).

tff(c_511,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_505])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_511])).

tff(c_515,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_843,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_862,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_843])).

tff(c_868,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_862])).

tff(c_870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:49:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.91/1.42  
% 2.91/1.42  %Foreground sorts:
% 2.91/1.42  
% 2.91/1.42  
% 2.91/1.42  %Background operators:
% 2.91/1.42  
% 2.91/1.42  
% 2.91/1.42  %Foreground operators:
% 2.91/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.91/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.91/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.42  
% 2.91/1.44  tff(f_95, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.91/1.44  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.91/1.44  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.91/1.44  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.91/1.44  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.91/1.44  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.91/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.91/1.44  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.91/1.44  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.91/1.44  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.91/1.44  tff(c_32, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.91/1.44  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.91/1.44  tff(c_47, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.91/1.44  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.91/1.44  tff(c_18, plain, (![A_12]: (k2_relat_1(A_12)=k1_xboole_0 | k1_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.91/1.44  tff(c_66, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_18])).
% 2.91/1.44  tff(c_67, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 2.91/1.44  tff(c_68, plain, (![A_46]: (k1_relat_1(A_46)=k1_xboole_0 | k2_relat_1(A_46)!=k1_xboole_0 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.91/1.44  tff(c_71, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_68])).
% 2.91/1.44  tff(c_74, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_67, c_71])).
% 2.91/1.44  tff(c_133, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.44  tff(c_147, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_133])).
% 2.91/1.44  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.91/1.44  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.91/1.44  tff(c_126, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.44  tff(c_149, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69), B_70) | ~r1_tarski(A_69, B_70) | k1_xboole_0=A_69)), inference(resolution, [status(thm)], [c_8, c_126])).
% 2.91/1.44  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.91/1.44  tff(c_161, plain, (![A_69, B_70]: (m1_subset_1('#skF_2'(A_69), B_70) | ~r1_tarski(A_69, B_70) | k1_xboole_0=A_69)), inference(resolution, [status(thm)], [c_149, c_10])).
% 2.91/1.44  tff(c_230, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.91/1.44  tff(c_254, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_230])).
% 2.91/1.44  tff(c_57, plain, (![D_45]: (~r2_hidden(D_45, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.91/1.44  tff(c_62, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_57])).
% 2.91/1.44  tff(c_98, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 2.91/1.44  tff(c_256, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_98])).
% 2.91/1.44  tff(c_264, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_256])).
% 2.91/1.44  tff(c_267, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_264])).
% 2.91/1.44  tff(c_270, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_267])).
% 2.91/1.44  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_147, c_270])).
% 2.91/1.44  tff(c_275, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 2.91/1.44  tff(c_486, plain, (![A_118, B_119, C_120]: (k2_relset_1(A_118, B_119, C_120)=k2_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.91/1.44  tff(c_505, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_486])).
% 2.91/1.44  tff(c_511, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_275, c_505])).
% 2.91/1.44  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_511])).
% 2.91/1.44  tff(c_515, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 2.91/1.44  tff(c_843, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.91/1.44  tff(c_862, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_843])).
% 2.91/1.44  tff(c_868, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_515, c_862])).
% 2.91/1.44  tff(c_870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_868])).
% 2.91/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.44  
% 2.91/1.44  Inference rules
% 2.91/1.44  ----------------------
% 2.91/1.44  #Ref     : 0
% 2.91/1.44  #Sup     : 161
% 2.91/1.44  #Fact    : 0
% 2.91/1.44  #Define  : 0
% 2.91/1.44  #Split   : 6
% 2.91/1.44  #Chain   : 0
% 2.91/1.44  #Close   : 0
% 2.91/1.44  
% 2.91/1.44  Ordering : KBO
% 2.91/1.44  
% 2.91/1.44  Simplification rules
% 2.91/1.44  ----------------------
% 2.91/1.44  #Subsume      : 5
% 2.91/1.44  #Demod        : 38
% 2.91/1.44  #Tautology    : 32
% 2.91/1.44  #SimpNegUnit  : 4
% 2.91/1.44  #BackRed      : 11
% 2.91/1.44  
% 2.91/1.44  #Partial instantiations: 0
% 2.91/1.44  #Strategies tried      : 1
% 2.91/1.44  
% 2.91/1.44  Timing (in seconds)
% 2.91/1.44  ----------------------
% 2.91/1.44  Preprocessing        : 0.31
% 2.91/1.44  Parsing              : 0.17
% 2.91/1.44  CNF conversion       : 0.02
% 2.91/1.44  Main loop            : 0.35
% 2.91/1.44  Inferencing          : 0.14
% 2.91/1.44  Reduction            : 0.10
% 2.91/1.44  Demodulation         : 0.06
% 2.91/1.44  BG Simplification    : 0.02
% 2.91/1.44  Subsumption          : 0.06
% 2.91/1.44  Abstraction          : 0.02
% 2.91/1.44  MUC search           : 0.00
% 2.91/1.44  Cooper               : 0.00
% 2.91/1.44  Total                : 0.70
% 2.91/1.44  Index Insertion      : 0.00
% 2.91/1.44  Index Deletion       : 0.00
% 2.91/1.44  Index Matching       : 0.00
% 2.91/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
