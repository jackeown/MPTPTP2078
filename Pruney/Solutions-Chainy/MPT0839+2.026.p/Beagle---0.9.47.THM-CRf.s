%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:25 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 163 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 306 expanded)
%              Number of equality atoms :   32 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_52,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_126,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77,B_78),A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [A_77] : r1_tarski(A_77,A_77) ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_81,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_81])).

tff(c_38,plain,(
    ! [A_35] :
      ( k1_relat_1(A_35) = k1_xboole_0
      | k2_relat_1(A_35) != k1_xboole_0
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_94,plain,
    ( k1_relat_1('#skF_8') = k1_xboole_0
    | k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_38])).

tff(c_100,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_95,plain,(
    ! [A_71] :
      ( k2_relat_1(A_71) = k1_xboole_0
      | k1_relat_1(A_71) != k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_95])).

tff(c_101,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_99])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1078,plain,(
    ! [A_234,B_235] :
      ( r2_hidden(k4_tarski('#skF_2'(A_234,B_235),'#skF_3'(A_234,B_235)),A_234)
      | r2_hidden('#skF_4'(A_234,B_235),B_235)
      | k1_relat_1(A_234) = B_235 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_382,plain,(
    ! [C_143,A_144] :
      ( r2_hidden(k4_tarski(C_143,'#skF_5'(A_144,k1_relat_1(A_144),C_143)),A_144)
      | ~ r2_hidden(C_143,k1_relat_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_407,plain,(
    ! [C_143] :
      ( r2_hidden(k4_tarski(C_143,'#skF_5'(k1_xboole_0,k1_xboole_0,C_143)),k1_xboole_0)
      | ~ r2_hidden(C_143,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_382])).

tff(c_441,plain,(
    ! [C_150] :
      ( r2_hidden(k4_tarski(C_150,'#skF_5'(k1_xboole_0,k1_xboole_0,C_150)),k1_xboole_0)
      | ~ r2_hidden(C_150,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_407])).

tff(c_42,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_451,plain,(
    ! [C_150] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_150,'#skF_5'(k1_xboole_0,k1_xboole_0,C_150)))
      | ~ r2_hidden(C_150,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_441,c_42])).

tff(c_462,plain,(
    ! [C_150] : ~ r2_hidden(C_150,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_451])).

tff(c_1087,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_235),B_235)
      | k1_relat_1(k1_xboole_0) = B_235 ) ),
    inference(resolution,[status(thm)],[c_1078,c_462])).

tff(c_1117,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_235),B_235)
      | k1_xboole_0 = B_235 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1087])).

tff(c_69,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1919,plain,(
    ! [C_268,A_269,B_270] :
      ( r2_hidden(k4_tarski(C_268,'#skF_5'(A_269,k1_relat_1(A_269),C_268)),B_270)
      | ~ r1_tarski(A_269,B_270)
      | ~ r2_hidden(C_268,k1_relat_1(A_269)) ) ),
    inference(resolution,[status(thm)],[c_382,c_2])).

tff(c_24,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8015,plain,(
    ! [C_401,B_402,A_403] :
      ( r2_hidden(C_401,k1_relat_1(B_402))
      | ~ r1_tarski(A_403,B_402)
      | ~ r2_hidden(C_401,k1_relat_1(A_403)) ) ),
    inference(resolution,[status(thm)],[c_1919,c_24])).

tff(c_8062,plain,(
    ! [C_404] :
      ( r2_hidden(C_404,k1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')))
      | ~ r2_hidden(C_404,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_73,c_8015])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_410,plain,(
    ! [C_143,C_9,D_10] :
      ( r2_hidden(C_143,C_9)
      | ~ r2_hidden(C_143,k1_relat_1(k2_zfmisc_1(C_9,D_10))) ) ),
    inference(resolution,[status(thm)],[c_382,c_14])).

tff(c_8139,plain,(
    ! [C_405] :
      ( r2_hidden(C_405,'#skF_7')
      | ~ r2_hidden(C_405,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_8062,c_410])).

tff(c_8205,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7')
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1117,c_8139])).

tff(c_8242,plain,(
    r2_hidden('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_8205])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_171,plain,(
    ! [A_99,C_100,B_101] :
      ( m1_subset_1(A_99,C_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(C_100))
      | ~ r2_hidden(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_176,plain,(
    ! [A_99,B_12,A_11] :
      ( m1_subset_1(A_99,B_12)
      | ~ r2_hidden(A_99,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_171])).

tff(c_9337,plain,(
    ! [B_430] :
      ( m1_subset_1('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),B_430)
      | ~ r1_tarski('#skF_7',B_430) ) ),
    inference(resolution,[status(thm)],[c_8242,c_176])).

tff(c_1126,plain,(
    ! [B_236] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_236),B_236)
      | k1_xboole_0 = B_236 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1087])).

tff(c_307,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_321,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_307])).

tff(c_50,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_58,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_324,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k1_relat_1('#skF_8'))
      | ~ m1_subset_1(D_58,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_50])).

tff(c_1143,plain,
    ( ~ m1_subset_1('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7')
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1126,c_324])).

tff(c_1158,plain,(
    ~ m1_subset_1('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1143])).

tff(c_9358,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_9337,c_1158])).

tff(c_9386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_9358])).

tff(c_9388,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_9535,plain,(
    ! [A_475,B_476,C_477] :
      ( k2_relset_1(A_475,B_476,C_477) = k2_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_475,B_476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9546,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_9535])).

tff(c_9550,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9388,c_9546])).

tff(c_9552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.63  
% 7.45/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.63  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.45/2.63  
% 7.45/2.63  %Foreground sorts:
% 7.45/2.63  
% 7.45/2.63  
% 7.45/2.63  %Background operators:
% 7.45/2.63  
% 7.45/2.63  
% 7.45/2.63  %Foreground operators:
% 7.45/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.45/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.45/2.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.45/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.45/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.45/2.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.45/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.45/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.45/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.45/2.63  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.45/2.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.45/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.63  tff('#skF_8', type, '#skF_8': $i).
% 7.45/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.45/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.45/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.45/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.45/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.45/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.45/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.45/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.63  
% 7.69/2.65  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 7.69/2.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.69/2.65  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.69/2.65  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.69/2.65  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.69/2.65  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 7.69/2.65  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.69/2.65  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.69/2.65  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.69/2.65  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.69/2.65  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.69/2.65  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.69/2.65  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.69/2.65  tff(c_52, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.69/2.65  tff(c_126, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77, B_78), A_77) | r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.65  tff(c_138, plain, (![A_77]: (r1_tarski(A_77, A_77))), inference(resolution, [status(thm)], [c_126, c_4])).
% 7.69/2.65  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.69/2.65  tff(c_81, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.69/2.65  tff(c_90, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_81])).
% 7.69/2.65  tff(c_38, plain, (![A_35]: (k1_relat_1(A_35)=k1_xboole_0 | k2_relat_1(A_35)!=k1_xboole_0 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.69/2.65  tff(c_94, plain, (k1_relat_1('#skF_8')=k1_xboole_0 | k2_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_38])).
% 7.69/2.65  tff(c_100, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 7.69/2.65  tff(c_95, plain, (![A_71]: (k2_relat_1(A_71)=k1_xboole_0 | k1_relat_1(A_71)!=k1_xboole_0 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.69/2.65  tff(c_99, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_95])).
% 7.69/2.65  tff(c_101, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_100, c_99])).
% 7.69/2.65  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.69/2.65  tff(c_1078, plain, (![A_234, B_235]: (r2_hidden(k4_tarski('#skF_2'(A_234, B_235), '#skF_3'(A_234, B_235)), A_234) | r2_hidden('#skF_4'(A_234, B_235), B_235) | k1_relat_1(A_234)=B_235)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.69/2.65  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.69/2.65  tff(c_382, plain, (![C_143, A_144]: (r2_hidden(k4_tarski(C_143, '#skF_5'(A_144, k1_relat_1(A_144), C_143)), A_144) | ~r2_hidden(C_143, k1_relat_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.69/2.65  tff(c_407, plain, (![C_143]: (r2_hidden(k4_tarski(C_143, '#skF_5'(k1_xboole_0, k1_xboole_0, C_143)), k1_xboole_0) | ~r2_hidden(C_143, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_382])).
% 7.69/2.65  tff(c_441, plain, (![C_150]: (r2_hidden(k4_tarski(C_150, '#skF_5'(k1_xboole_0, k1_xboole_0, C_150)), k1_xboole_0) | ~r2_hidden(C_150, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_407])).
% 7.69/2.65  tff(c_42, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.69/2.65  tff(c_451, plain, (![C_150]: (~r1_tarski(k1_xboole_0, k4_tarski(C_150, '#skF_5'(k1_xboole_0, k1_xboole_0, C_150))) | ~r2_hidden(C_150, k1_xboole_0))), inference(resolution, [status(thm)], [c_441, c_42])).
% 7.69/2.65  tff(c_462, plain, (![C_150]: (~r2_hidden(C_150, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_451])).
% 7.69/2.65  tff(c_1087, plain, (![B_235]: (r2_hidden('#skF_4'(k1_xboole_0, B_235), B_235) | k1_relat_1(k1_xboole_0)=B_235)), inference(resolution, [status(thm)], [c_1078, c_462])).
% 7.69/2.65  tff(c_1117, plain, (![B_235]: (r2_hidden('#skF_4'(k1_xboole_0, B_235), B_235) | k1_xboole_0=B_235)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1087])).
% 7.69/2.65  tff(c_69, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.69/2.65  tff(c_73, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_69])).
% 7.69/2.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.65  tff(c_1919, plain, (![C_268, A_269, B_270]: (r2_hidden(k4_tarski(C_268, '#skF_5'(A_269, k1_relat_1(A_269), C_268)), B_270) | ~r1_tarski(A_269, B_270) | ~r2_hidden(C_268, k1_relat_1(A_269)))), inference(resolution, [status(thm)], [c_382, c_2])).
% 7.69/2.65  tff(c_24, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.69/2.65  tff(c_8015, plain, (![C_401, B_402, A_403]: (r2_hidden(C_401, k1_relat_1(B_402)) | ~r1_tarski(A_403, B_402) | ~r2_hidden(C_401, k1_relat_1(A_403)))), inference(resolution, [status(thm)], [c_1919, c_24])).
% 7.69/2.65  tff(c_8062, plain, (![C_404]: (r2_hidden(C_404, k1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~r2_hidden(C_404, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_73, c_8015])).
% 7.69/2.65  tff(c_14, plain, (![A_7, C_9, B_8, D_10]: (r2_hidden(A_7, C_9) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.69/2.65  tff(c_410, plain, (![C_143, C_9, D_10]: (r2_hidden(C_143, C_9) | ~r2_hidden(C_143, k1_relat_1(k2_zfmisc_1(C_9, D_10))))), inference(resolution, [status(thm)], [c_382, c_14])).
% 7.69/2.65  tff(c_8139, plain, (![C_405]: (r2_hidden(C_405, '#skF_7') | ~r2_hidden(C_405, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_8062, c_410])).
% 7.69/2.65  tff(c_8205, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7') | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_1117, c_8139])).
% 7.69/2.65  tff(c_8242, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_101, c_8205])).
% 7.69/2.65  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.69/2.65  tff(c_171, plain, (![A_99, C_100, B_101]: (m1_subset_1(A_99, C_100) | ~m1_subset_1(B_101, k1_zfmisc_1(C_100)) | ~r2_hidden(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.69/2.65  tff(c_176, plain, (![A_99, B_12, A_11]: (m1_subset_1(A_99, B_12) | ~r2_hidden(A_99, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_171])).
% 7.69/2.65  tff(c_9337, plain, (![B_430]: (m1_subset_1('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), B_430) | ~r1_tarski('#skF_7', B_430))), inference(resolution, [status(thm)], [c_8242, c_176])).
% 7.69/2.65  tff(c_1126, plain, (![B_236]: (r2_hidden('#skF_4'(k1_xboole_0, B_236), B_236) | k1_xboole_0=B_236)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1087])).
% 7.69/2.65  tff(c_307, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.69/2.65  tff(c_321, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_307])).
% 7.69/2.65  tff(c_50, plain, (![D_58]: (~r2_hidden(D_58, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_58, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.69/2.65  tff(c_324, plain, (![D_58]: (~r2_hidden(D_58, k1_relat_1('#skF_8')) | ~m1_subset_1(D_58, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_50])).
% 7.69/2.65  tff(c_1143, plain, (~m1_subset_1('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7') | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_1126, c_324])).
% 7.69/2.65  tff(c_1158, plain, (~m1_subset_1('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_101, c_1143])).
% 7.69/2.65  tff(c_9358, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_9337, c_1158])).
% 7.69/2.65  tff(c_9386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_9358])).
% 7.69/2.65  tff(c_9388, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 7.69/2.65  tff(c_9535, plain, (![A_475, B_476, C_477]: (k2_relset_1(A_475, B_476, C_477)=k2_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.65  tff(c_9546, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_9535])).
% 7.69/2.65  tff(c_9550, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9388, c_9546])).
% 7.69/2.65  tff(c_9552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_9550])).
% 7.69/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.65  
% 7.69/2.65  Inference rules
% 7.69/2.65  ----------------------
% 7.69/2.65  #Ref     : 0
% 7.69/2.65  #Sup     : 2209
% 7.69/2.65  #Fact    : 0
% 7.69/2.65  #Define  : 0
% 7.69/2.65  #Split   : 5
% 7.69/2.65  #Chain   : 0
% 7.69/2.65  #Close   : 0
% 7.69/2.65  
% 7.69/2.65  Ordering : KBO
% 7.69/2.65  
% 7.69/2.65  Simplification rules
% 7.69/2.65  ----------------------
% 7.69/2.65  #Subsume      : 630
% 7.69/2.65  #Demod        : 1220
% 7.69/2.65  #Tautology    : 665
% 7.69/2.65  #SimpNegUnit  : 42
% 7.69/2.65  #BackRed      : 9
% 7.69/2.65  
% 7.69/2.65  #Partial instantiations: 0
% 7.69/2.65  #Strategies tried      : 1
% 7.69/2.65  
% 7.69/2.65  Timing (in seconds)
% 7.69/2.65  ----------------------
% 7.69/2.65  Preprocessing        : 0.31
% 7.69/2.65  Parsing              : 0.15
% 7.69/2.65  CNF conversion       : 0.03
% 7.69/2.65  Main loop            : 1.56
% 7.69/2.65  Inferencing          : 0.47
% 7.69/2.65  Reduction            : 0.45
% 7.69/2.65  Demodulation         : 0.30
% 7.69/2.65  BG Simplification    : 0.06
% 7.69/2.65  Subsumption          : 0.47
% 7.69/2.65  Abstraction          : 0.08
% 7.69/2.65  MUC search           : 0.00
% 7.69/2.65  Cooper               : 0.00
% 7.69/2.65  Total                : 1.91
% 7.69/2.65  Index Insertion      : 0.00
% 7.69/2.65  Index Deletion       : 0.00
% 7.69/2.65  Index Matching       : 0.00
% 7.69/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
