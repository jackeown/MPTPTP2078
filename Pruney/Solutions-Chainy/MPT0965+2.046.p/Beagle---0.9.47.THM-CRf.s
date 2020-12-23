%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:06 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 106 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 213 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_331,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_335,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_331])).

tff(c_742,plain,(
    ! [B_153,A_154,C_155] :
      ( k1_xboole_0 = B_153
      | k1_relset_1(A_154,B_153,C_155) = A_154
      | ~ v1_funct_2(C_155,A_154,B_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_749,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_742])).

tff(c_753,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_335,c_749])).

tff(c_754,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_753])).

tff(c_74,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | v1_xboole_0(B_47)
      | ~ m1_subset_1(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_48])).

tff(c_88,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_52,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_155,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_5',B_63)
      | ~ r1_tarski('#skF_3',B_63) ) ),
    inference(resolution,[status(thm)],[c_52,c_155])).

tff(c_26,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_107,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_104])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_522,plain,(
    ! [B_126,A_127] :
      ( r2_hidden(k1_funct_1(B_126,A_127),k2_relat_1(B_126))
      | ~ r2_hidden(A_127,k1_relat_1(B_126))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_381,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_385,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_381])).

tff(c_435,plain,(
    ! [A_120,B_121,C_122] :
      ( m1_subset_1(k2_relset_1(A_120,B_121,C_122),k1_zfmisc_1(B_121))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_453,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_435])).

tff(c_460,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_453])).

tff(c_22,plain,(
    ! [A_15,C_17,B_16] :
      ( m1_subset_1(A_15,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_469,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,'#skF_4')
      | ~ r2_hidden(A_15,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_460,c_22])).

tff(c_526,plain,(
    ! [A_127] :
      ( m1_subset_1(k1_funct_1('#skF_6',A_127),'#skF_4')
      | ~ r2_hidden(A_127,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_522,c_469])).

tff(c_550,plain,(
    ! [A_130] :
      ( m1_subset_1(k1_funct_1('#skF_6',A_130),'#skF_4')
      | ~ r2_hidden(A_130,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_58,c_526])).

tff(c_578,plain,
    ( m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_167,c_550])).

tff(c_591,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_578])).

tff(c_761,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_591])).

tff(c_766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_761])).

tff(c_767,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_769,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_2'(A_156,B_157),A_156)
      | r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_779,plain,(
    ! [A_156,B_157] :
      ( ~ v1_xboole_0(A_156)
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_769,c_2])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_788,plain,(
    ! [B_162,A_163] :
      ( B_162 = A_163
      | ~ r1_tarski(B_162,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_801,plain,(
    ! [A_164] :
      ( k1_xboole_0 = A_164
      | ~ r1_tarski(A_164,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_788])).

tff(c_832,plain,(
    ! [A_168] :
      ( k1_xboole_0 = A_168
      | ~ v1_xboole_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_779,c_801])).

tff(c_835,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_767,c_832])).

tff(c_839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:51:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.23/1.49  
% 3.23/1.49  %Foreground sorts:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Background operators:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Foreground operators:
% 3.23/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.23/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.23/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.23/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.49  
% 3.23/1.50  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.23/1.50  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.50  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.23/1.50  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.23/1.50  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.23/1.50  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.50  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.23/1.50  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.23/1.50  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.23/1.50  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.23/1.50  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.23/1.50  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.23/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.23/1.50  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.50  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.50  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.50  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.50  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.50  tff(c_331, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.50  tff(c_335, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_331])).
% 3.23/1.50  tff(c_742, plain, (![B_153, A_154, C_155]: (k1_xboole_0=B_153 | k1_relset_1(A_154, B_153, C_155)=A_154 | ~v1_funct_2(C_155, A_154, B_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.50  tff(c_749, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_742])).
% 3.23/1.50  tff(c_753, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_335, c_749])).
% 3.23/1.50  tff(c_754, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_753])).
% 3.23/1.50  tff(c_74, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | v1_xboole_0(B_47) | ~m1_subset_1(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.50  tff(c_48, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.50  tff(c_86, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_74, c_48])).
% 3.23/1.50  tff(c_88, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 3.23/1.50  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.50  tff(c_155, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.50  tff(c_167, plain, (![B_63]: (r2_hidden('#skF_5', B_63) | ~r1_tarski('#skF_3', B_63))), inference(resolution, [status(thm)], [c_52, c_155])).
% 3.23/1.50  tff(c_26, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.23/1.50  tff(c_101, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.50  tff(c_104, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_101])).
% 3.23/1.50  tff(c_107, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_104])).
% 3.23/1.50  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.23/1.50  tff(c_522, plain, (![B_126, A_127]: (r2_hidden(k1_funct_1(B_126, A_127), k2_relat_1(B_126)) | ~r2_hidden(A_127, k1_relat_1(B_126)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.50  tff(c_381, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.23/1.50  tff(c_385, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_381])).
% 3.23/1.50  tff(c_435, plain, (![A_120, B_121, C_122]: (m1_subset_1(k2_relset_1(A_120, B_121, C_122), k1_zfmisc_1(B_121)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.50  tff(c_453, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_385, c_435])).
% 3.23/1.50  tff(c_460, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_453])).
% 3.23/1.50  tff(c_22, plain, (![A_15, C_17, B_16]: (m1_subset_1(A_15, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.50  tff(c_469, plain, (![A_15]: (m1_subset_1(A_15, '#skF_4') | ~r2_hidden(A_15, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_460, c_22])).
% 3.23/1.50  tff(c_526, plain, (![A_127]: (m1_subset_1(k1_funct_1('#skF_6', A_127), '#skF_4') | ~r2_hidden(A_127, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_522, c_469])).
% 3.23/1.50  tff(c_550, plain, (![A_130]: (m1_subset_1(k1_funct_1('#skF_6', A_130), '#skF_4') | ~r2_hidden(A_130, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_58, c_526])).
% 3.23/1.50  tff(c_578, plain, (m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_167, c_550])).
% 3.23/1.50  tff(c_591, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_88, c_578])).
% 3.23/1.50  tff(c_761, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_591])).
% 3.23/1.50  tff(c_766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_761])).
% 3.23/1.50  tff(c_767, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 3.23/1.50  tff(c_769, plain, (![A_156, B_157]: (r2_hidden('#skF_2'(A_156, B_157), A_156) | r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.50  tff(c_779, plain, (![A_156, B_157]: (~v1_xboole_0(A_156) | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_769, c_2])).
% 3.23/1.50  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.50  tff(c_788, plain, (![B_162, A_163]: (B_162=A_163 | ~r1_tarski(B_162, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.50  tff(c_801, plain, (![A_164]: (k1_xboole_0=A_164 | ~r1_tarski(A_164, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_788])).
% 3.23/1.51  tff(c_832, plain, (![A_168]: (k1_xboole_0=A_168 | ~v1_xboole_0(A_168))), inference(resolution, [status(thm)], [c_779, c_801])).
% 3.23/1.51  tff(c_835, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_767, c_832])).
% 3.23/1.51  tff(c_839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_835])).
% 3.23/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  Inference rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Ref     : 0
% 3.23/1.51  #Sup     : 165
% 3.23/1.51  #Fact    : 0
% 3.23/1.51  #Define  : 0
% 3.23/1.51  #Split   : 14
% 3.23/1.51  #Chain   : 0
% 3.23/1.51  #Close   : 0
% 3.23/1.51  
% 3.23/1.51  Ordering : KBO
% 3.23/1.51  
% 3.23/1.51  Simplification rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Subsume      : 53
% 3.23/1.51  #Demod        : 27
% 3.23/1.51  #Tautology    : 23
% 3.23/1.51  #SimpNegUnit  : 10
% 3.23/1.51  #BackRed      : 12
% 3.23/1.51  
% 3.23/1.51  #Partial instantiations: 0
% 3.23/1.51  #Strategies tried      : 1
% 3.23/1.51  
% 3.23/1.51  Timing (in seconds)
% 3.23/1.51  ----------------------
% 3.39/1.51  Preprocessing        : 0.34
% 3.39/1.51  Parsing              : 0.18
% 3.39/1.51  CNF conversion       : 0.02
% 3.39/1.51  Main loop            : 0.42
% 3.39/1.51  Inferencing          : 0.15
% 3.39/1.51  Reduction            : 0.12
% 3.39/1.51  Demodulation         : 0.08
% 3.39/1.51  BG Simplification    : 0.02
% 3.39/1.51  Subsumption          : 0.09
% 3.39/1.51  Abstraction          : 0.02
% 3.39/1.51  MUC search           : 0.00
% 3.39/1.51  Cooper               : 0.00
% 3.39/1.51  Total                : 0.79
% 3.39/1.51  Index Insertion      : 0.00
% 3.39/1.51  Index Deletion       : 0.00
% 3.39/1.51  Index Matching       : 0.00
% 3.39/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
