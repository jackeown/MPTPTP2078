%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 144 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_340,plain,(
    ! [B_84,A_85] :
      ( r1_xboole_0(k2_relat_1(B_84),A_85)
      | k10_relat_1(B_84,A_85) != k1_xboole_0
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_751,plain,(
    ! [A_126,A_127,B_128] :
      ( r1_xboole_0(A_126,A_127)
      | ~ r1_tarski(A_126,k2_relat_1(B_128))
      | k10_relat_1(B_128,A_127) != k1_xboole_0
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_340,c_22])).

tff(c_774,plain,(
    ! [A_127] :
      ( r1_xboole_0('#skF_5',A_127)
      | k10_relat_1('#skF_6',A_127) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_751])).

tff(c_789,plain,(
    ! [A_129] :
      ( r1_xboole_0('#skF_5',A_129)
      | k10_relat_1('#skF_6',A_129) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_774])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_xboole_0(B_16,A_15)
      | ~ r1_tarski(B_16,A_15)
      | v1_xboole_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_796,plain,(
    ! [A_129] :
      ( ~ r1_tarski('#skF_5',A_129)
      | v1_xboole_0('#skF_5')
      | k10_relat_1('#skF_6',A_129) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_789,c_24])).

tff(c_871,plain,(
    ! [A_136] :
      ( ~ r1_tarski('#skF_5',A_136)
      | k10_relat_1('#skF_6',A_136) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_878,plain,(
    k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_871])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_878])).

tff(c_884,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_40,plain,(
    ! [A_23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_91,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ! [A_45,A_17] :
      ( r1_tarski(A_45,A_17)
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_91,c_26])).

tff(c_114,plain,(
    ! [A_49,A_50] :
      ( r1_tarski(A_49,A_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_95])).

tff(c_118,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(resolution,[status(thm)],[c_40,c_114])).

tff(c_192,plain,(
    ! [A_61,B_62] :
      ( r2_xboole_0(A_61,B_62)
      | B_62 = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),B_55)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [B_55,A_54] :
      ( ~ v1_xboole_0(B_55)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_210,plain,(
    ! [B_63,A_64] :
      ( ~ v1_xboole_0(B_63)
      | B_63 = A_64
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_192,c_135])).

tff(c_223,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(resolution,[status(thm)],[c_118,c_210])).

tff(c_894,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_884,c_223])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:54:09 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.47  
% 3.09/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.48  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.09/1.48  
% 3.09/1.48  %Foreground sorts:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Background operators:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Foreground operators:
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.09/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.48  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.09/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.09/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.48  
% 3.09/1.49  tff(f_109, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 3.09/1.49  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.49  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.09/1.49  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.09/1.49  tff(f_68, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.09/1.49  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.09/1.49  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.09/1.49  tff(f_86, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.09/1.49  tff(f_75, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.09/1.49  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.09/1.49  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.09/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.09/1.49  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.49  tff(c_50, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.49  tff(c_20, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.49  tff(c_56, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.49  tff(c_52, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.49  tff(c_340, plain, (![B_84, A_85]: (r1_xboole_0(k2_relat_1(B_84), A_85) | k10_relat_1(B_84, A_85)!=k1_xboole_0 | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.09/1.49  tff(c_22, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.49  tff(c_751, plain, (![A_126, A_127, B_128]: (r1_xboole_0(A_126, A_127) | ~r1_tarski(A_126, k2_relat_1(B_128)) | k10_relat_1(B_128, A_127)!=k1_xboole_0 | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_340, c_22])).
% 3.09/1.49  tff(c_774, plain, (![A_127]: (r1_xboole_0('#skF_5', A_127) | k10_relat_1('#skF_6', A_127)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_751])).
% 3.09/1.49  tff(c_789, plain, (![A_129]: (r1_xboole_0('#skF_5', A_129) | k10_relat_1('#skF_6', A_129)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_774])).
% 3.09/1.49  tff(c_24, plain, (![B_16, A_15]: (~r1_xboole_0(B_16, A_15) | ~r1_tarski(B_16, A_15) | v1_xboole_0(B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.49  tff(c_796, plain, (![A_129]: (~r1_tarski('#skF_5', A_129) | v1_xboole_0('#skF_5') | k10_relat_1('#skF_6', A_129)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_789, c_24])).
% 3.09/1.49  tff(c_871, plain, (![A_136]: (~r1_tarski('#skF_5', A_136) | k10_relat_1('#skF_6', A_136)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_796])).
% 3.09/1.49  tff(c_878, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_871])).
% 3.09/1.49  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_878])).
% 3.09/1.49  tff(c_884, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_796])).
% 3.09/1.49  tff(c_40, plain, (![A_23]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.49  tff(c_38, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.49  tff(c_91, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.49  tff(c_26, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.09/1.49  tff(c_95, plain, (![A_45, A_17]: (r1_tarski(A_45, A_17) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_91, c_26])).
% 3.09/1.49  tff(c_114, plain, (![A_49, A_50]: (r1_tarski(A_49, A_50) | ~m1_subset_1(A_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_38, c_95])).
% 3.09/1.49  tff(c_118, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(resolution, [status(thm)], [c_40, c_114])).
% 3.09/1.49  tff(c_192, plain, (![A_61, B_62]: (r2_xboole_0(A_61, B_62) | B_62=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.49  tff(c_121, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), B_55) | ~r2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.49  tff(c_135, plain, (![B_55, A_54]: (~v1_xboole_0(B_55) | ~r2_xboole_0(A_54, B_55))), inference(resolution, [status(thm)], [c_121, c_2])).
% 3.09/1.49  tff(c_210, plain, (![B_63, A_64]: (~v1_xboole_0(B_63) | B_63=A_64 | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_192, c_135])).
% 3.09/1.49  tff(c_223, plain, (![A_23]: (~v1_xboole_0(A_23) | k1_xboole_0=A_23)), inference(resolution, [status(thm)], [c_118, c_210])).
% 3.09/1.49  tff(c_894, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_884, c_223])).
% 3.09/1.49  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_894])).
% 3.09/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  Inference rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Ref     : 0
% 3.09/1.49  #Sup     : 178
% 3.09/1.49  #Fact    : 0
% 3.09/1.49  #Define  : 0
% 3.09/1.49  #Split   : 7
% 3.09/1.49  #Chain   : 0
% 3.09/1.49  #Close   : 0
% 3.09/1.49  
% 3.09/1.49  Ordering : KBO
% 3.09/1.49  
% 3.09/1.49  Simplification rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Subsume      : 27
% 3.09/1.49  #Demod        : 49
% 3.09/1.49  #Tautology    : 46
% 3.09/1.49  #SimpNegUnit  : 11
% 3.09/1.49  #BackRed      : 4
% 3.09/1.49  
% 3.09/1.49  #Partial instantiations: 0
% 3.09/1.49  #Strategies tried      : 1
% 3.09/1.49  
% 3.09/1.49  Timing (in seconds)
% 3.09/1.49  ----------------------
% 3.09/1.49  Preprocessing        : 0.33
% 3.09/1.49  Parsing              : 0.18
% 3.09/1.49  CNF conversion       : 0.02
% 3.09/1.49  Main loop            : 0.38
% 3.09/1.49  Inferencing          : 0.14
% 3.09/1.49  Reduction            : 0.11
% 3.09/1.49  Demodulation         : 0.07
% 3.09/1.49  BG Simplification    : 0.02
% 3.09/1.49  Subsumption          : 0.08
% 3.09/1.49  Abstraction          : 0.02
% 3.09/1.49  MUC search           : 0.00
% 3.09/1.50  Cooper               : 0.00
% 3.09/1.50  Total                : 0.74
% 3.09/1.50  Index Insertion      : 0.00
% 3.09/1.50  Index Deletion       : 0.00
% 3.09/1.50  Index Matching       : 0.00
% 3.09/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
