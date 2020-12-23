%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 10.61s
% Output     : CNFRefutation 10.61s
% Verified   : 
% Statistics : Number of formulae       :   69 (  97 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 171 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_52,plain,
    ( k10_relat_1('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_91,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | k10_relat_1('#skF_6',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_122,plain,(
    k10_relat_1('#skF_6',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_58])).

tff(c_110,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,(
    ! [A_45,A_14] :
      ( '#skF_1'(A_45,k1_tarski(A_14)) = A_14
      | r1_xboole_0(A_45,k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_110,c_18])).

tff(c_374,plain,(
    ! [B_78,A_79] :
      ( k10_relat_1(B_78,A_79) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_78),A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4666,plain,(
    ! [B_1783,A_1784] :
      ( k10_relat_1(B_1783,k1_tarski(A_1784)) = k1_xboole_0
      | ~ v1_relat_1(B_1783)
      | '#skF_1'(k2_relat_1(B_1783),k1_tarski(A_1784)) = A_1784 ) ),
    inference(resolution,[status(thm)],[c_115,c_374])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22973,plain,(
    ! [A_9232,B_9233] :
      ( r2_hidden(A_9232,k2_relat_1(B_9233))
      | r1_xboole_0(k2_relat_1(B_9233),k1_tarski(A_9232))
      | k10_relat_1(B_9233,k1_tarski(A_9232)) = k1_xboole_0
      | ~ v1_relat_1(B_9233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4666,c_10])).

tff(c_40,plain,(
    ! [B_27,A_26] :
      ( k10_relat_1(B_27,A_26) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_23280,plain,(
    ! [A_9327,B_9328] :
      ( r2_hidden(A_9327,k2_relat_1(B_9328))
      | k10_relat_1(B_9328,k1_tarski(A_9327)) = k1_xboole_0
      | ~ v1_relat_1(B_9328) ) ),
    inference(resolution,[status(thm)],[c_22973,c_40])).

tff(c_23387,plain,
    ( k10_relat_1('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_23280,c_91])).

tff(c_23445,plain,(
    k10_relat_1('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_23387])).

tff(c_23447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_23445])).

tff(c_23448,plain,(
    k10_relat_1('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_23449,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_23480,plain,(
    ! [A_9386,B_9387,C_9388] :
      ( ~ r1_xboole_0(A_9386,B_9387)
      | ~ r2_hidden(C_9388,k3_xboole_0(A_9386,B_9387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_23487,plain,(
    ! [A_13,C_9388] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_9388,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_23480])).

tff(c_23489,plain,(
    ! [C_9388] : ~ r2_hidden(C_9388,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_23487])).

tff(c_23502,plain,(
    ! [A_9391,B_9392] :
      ( r2_hidden('#skF_1'(A_9391,B_9392),A_9391)
      | r1_xboole_0(A_9391,B_9392) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23518,plain,(
    ! [B_9393] : r1_xboole_0(k1_xboole_0,B_9393) ),
    inference(resolution,[status(thm)],[c_23502,c_23489])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23522,plain,(
    ! [B_9393] : k3_xboole_0(k1_xboole_0,B_9393) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23518,c_2])).

tff(c_23563,plain,(
    ! [B_9398,A_9399] :
      ( r2_hidden(B_9398,A_9399)
      | k3_xboole_0(A_9399,k1_tarski(B_9398)) != k1_tarski(B_9398) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_23567,plain,(
    ! [B_9398] :
      ( r2_hidden(B_9398,k1_xboole_0)
      | k1_tarski(B_9398) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23522,c_23563])).

tff(c_23568,plain,(
    ! [B_9398] : k1_tarski(B_9398) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_23489,c_23567])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_tarski(A_19),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24920,plain,(
    ! [B_10328,A_10329] :
      ( k10_relat_1(B_10328,A_10329) != k1_xboole_0
      | ~ r1_tarski(A_10329,k2_relat_1(B_10328))
      | k1_xboole_0 = A_10329
      | ~ v1_relat_1(B_10328) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24925,plain,(
    ! [B_10328,A_19] :
      ( k10_relat_1(B_10328,k1_tarski(A_19)) != k1_xboole_0
      | k1_tarski(A_19) = k1_xboole_0
      | ~ v1_relat_1(B_10328)
      | ~ r2_hidden(A_19,k2_relat_1(B_10328)) ) ),
    inference(resolution,[status(thm)],[c_32,c_24920])).

tff(c_24941,plain,(
    ! [B_10361,A_10362] :
      ( k10_relat_1(B_10361,k1_tarski(A_10362)) != k1_xboole_0
      | ~ v1_relat_1(B_10361)
      | ~ r2_hidden(A_10362,k2_relat_1(B_10361)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_23568,c_24925])).

tff(c_24957,plain,
    ( k10_relat_1('#skF_6',k1_tarski('#skF_5')) != k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_23449,c_24941])).

tff(c_24967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_23448,c_24957])).

tff(c_24969,plain,(
    ! [A_10378] : ~ r1_xboole_0(A_10378,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_23487])).

tff(c_24973,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_24969])).

tff(c_24977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.61/4.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.61/4.08  
% 10.61/4.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.61/4.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 10.61/4.08  
% 10.61/4.08  %Foreground sorts:
% 10.61/4.08  
% 10.61/4.08  
% 10.61/4.08  %Background operators:
% 10.61/4.08  
% 10.61/4.08  
% 10.61/4.08  %Foreground operators:
% 10.61/4.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.61/4.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.61/4.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.61/4.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.61/4.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.61/4.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.61/4.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.61/4.08  tff('#skF_5', type, '#skF_5': $i).
% 10.61/4.08  tff('#skF_6', type, '#skF_6': $i).
% 10.61/4.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.61/4.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.61/4.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.61/4.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.61/4.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.61/4.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.61/4.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.61/4.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.61/4.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.61/4.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.61/4.08  
% 10.61/4.09  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 10.61/4.09  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.61/4.09  tff(f_111, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 10.61/4.09  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.61/4.09  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.61/4.09  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 10.61/4.09  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.61/4.09  tff(f_78, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 10.61/4.09  tff(f_74, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.61/4.09  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 10.61/4.09  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.61/4.09  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.61/4.09  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.61/4.09  tff(c_52, plain, (k10_relat_1('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0 | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.61/4.09  tff(c_91, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_52])).
% 10.61/4.09  tff(c_58, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6')) | k10_relat_1('#skF_6', k1_tarski('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.61/4.09  tff(c_122, plain, (k10_relat_1('#skF_6', k1_tarski('#skF_5'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_91, c_58])).
% 10.61/4.09  tff(c_110, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/4.09  tff(c_18, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.61/4.09  tff(c_115, plain, (![A_45, A_14]: ('#skF_1'(A_45, k1_tarski(A_14))=A_14 | r1_xboole_0(A_45, k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_110, c_18])).
% 10.61/4.09  tff(c_374, plain, (![B_78, A_79]: (k10_relat_1(B_78, A_79)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_78), A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.61/4.09  tff(c_4666, plain, (![B_1783, A_1784]: (k10_relat_1(B_1783, k1_tarski(A_1784))=k1_xboole_0 | ~v1_relat_1(B_1783) | '#skF_1'(k2_relat_1(B_1783), k1_tarski(A_1784))=A_1784)), inference(resolution, [status(thm)], [c_115, c_374])).
% 10.61/4.09  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/4.09  tff(c_22973, plain, (![A_9232, B_9233]: (r2_hidden(A_9232, k2_relat_1(B_9233)) | r1_xboole_0(k2_relat_1(B_9233), k1_tarski(A_9232)) | k10_relat_1(B_9233, k1_tarski(A_9232))=k1_xboole_0 | ~v1_relat_1(B_9233))), inference(superposition, [status(thm), theory('equality')], [c_4666, c_10])).
% 10.61/4.09  tff(c_40, plain, (![B_27, A_26]: (k10_relat_1(B_27, A_26)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.61/4.09  tff(c_23280, plain, (![A_9327, B_9328]: (r2_hidden(A_9327, k2_relat_1(B_9328)) | k10_relat_1(B_9328, k1_tarski(A_9327))=k1_xboole_0 | ~v1_relat_1(B_9328))), inference(resolution, [status(thm)], [c_22973, c_40])).
% 10.61/4.09  tff(c_23387, plain, (k10_relat_1('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_23280, c_91])).
% 10.61/4.09  tff(c_23445, plain, (k10_relat_1('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_23387])).
% 10.61/4.09  tff(c_23447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_23445])).
% 10.61/4.09  tff(c_23448, plain, (k10_relat_1('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 10.61/4.09  tff(c_23449, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_52])).
% 10.61/4.09  tff(c_23480, plain, (![A_9386, B_9387, C_9388]: (~r1_xboole_0(A_9386, B_9387) | ~r2_hidden(C_9388, k3_xboole_0(A_9386, B_9387)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.61/4.09  tff(c_23487, plain, (![A_13, C_9388]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_9388, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_23480])).
% 10.61/4.09  tff(c_23489, plain, (![C_9388]: (~r2_hidden(C_9388, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_23487])).
% 10.61/4.09  tff(c_23502, plain, (![A_9391, B_9392]: (r2_hidden('#skF_1'(A_9391, B_9392), A_9391) | r1_xboole_0(A_9391, B_9392))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/4.09  tff(c_23518, plain, (![B_9393]: (r1_xboole_0(k1_xboole_0, B_9393))), inference(resolution, [status(thm)], [c_23502, c_23489])).
% 10.61/4.09  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.61/4.09  tff(c_23522, plain, (![B_9393]: (k3_xboole_0(k1_xboole_0, B_9393)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23518, c_2])).
% 10.61/4.09  tff(c_23563, plain, (![B_9398, A_9399]: (r2_hidden(B_9398, A_9399) | k3_xboole_0(A_9399, k1_tarski(B_9398))!=k1_tarski(B_9398))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.61/4.09  tff(c_23567, plain, (![B_9398]: (r2_hidden(B_9398, k1_xboole_0) | k1_tarski(B_9398)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23522, c_23563])).
% 10.61/4.09  tff(c_23568, plain, (![B_9398]: (k1_tarski(B_9398)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_23489, c_23567])).
% 10.61/4.09  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.61/4.09  tff(c_24920, plain, (![B_10328, A_10329]: (k10_relat_1(B_10328, A_10329)!=k1_xboole_0 | ~r1_tarski(A_10329, k2_relat_1(B_10328)) | k1_xboole_0=A_10329 | ~v1_relat_1(B_10328))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.61/4.09  tff(c_24925, plain, (![B_10328, A_19]: (k10_relat_1(B_10328, k1_tarski(A_19))!=k1_xboole_0 | k1_tarski(A_19)=k1_xboole_0 | ~v1_relat_1(B_10328) | ~r2_hidden(A_19, k2_relat_1(B_10328)))), inference(resolution, [status(thm)], [c_32, c_24920])).
% 10.61/4.09  tff(c_24941, plain, (![B_10361, A_10362]: (k10_relat_1(B_10361, k1_tarski(A_10362))!=k1_xboole_0 | ~v1_relat_1(B_10361) | ~r2_hidden(A_10362, k2_relat_1(B_10361)))), inference(negUnitSimplification, [status(thm)], [c_23568, c_24925])).
% 10.61/4.09  tff(c_24957, plain, (k10_relat_1('#skF_6', k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_23449, c_24941])).
% 10.61/4.09  tff(c_24967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_23448, c_24957])).
% 10.61/4.09  tff(c_24969, plain, (![A_10378]: (~r1_xboole_0(A_10378, k1_xboole_0))), inference(splitRight, [status(thm)], [c_23487])).
% 10.61/4.09  tff(c_24973, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_24969])).
% 10.61/4.09  tff(c_24977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_24973])).
% 10.61/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.61/4.09  
% 10.61/4.09  Inference rules
% 10.61/4.09  ----------------------
% 10.61/4.09  #Ref     : 0
% 10.61/4.09  #Sup     : 4864
% 10.61/4.09  #Fact    : 4
% 10.61/4.09  #Define  : 0
% 10.61/4.09  #Split   : 10
% 10.61/4.09  #Chain   : 0
% 10.61/4.09  #Close   : 0
% 10.61/4.09  
% 10.61/4.09  Ordering : KBO
% 10.61/4.09  
% 10.61/4.09  Simplification rules
% 10.61/4.09  ----------------------
% 10.61/4.09  #Subsume      : 1342
% 10.61/4.09  #Demod        : 812
% 10.61/4.09  #Tautology    : 1332
% 10.61/4.09  #SimpNegUnit  : 49
% 10.61/4.09  #BackRed      : 1
% 10.61/4.09  
% 10.61/4.09  #Partial instantiations: 7860
% 10.61/4.09  #Strategies tried      : 1
% 10.61/4.09  
% 10.61/4.09  Timing (in seconds)
% 10.61/4.09  ----------------------
% 10.61/4.10  Preprocessing        : 0.30
% 10.61/4.10  Parsing              : 0.17
% 10.61/4.10  CNF conversion       : 0.02
% 10.61/4.10  Main loop            : 3.03
% 10.61/4.10  Inferencing          : 1.03
% 10.61/4.10  Reduction            : 0.66
% 10.61/4.10  Demodulation         : 0.42
% 10.61/4.10  BG Simplification    : 0.12
% 10.61/4.10  Subsumption          : 1.04
% 10.61/4.10  Abstraction          : 0.17
% 10.61/4.10  MUC search           : 0.00
% 10.61/4.10  Cooper               : 0.00
% 10.61/4.10  Total                : 3.36
% 10.61/4.10  Index Insertion      : 0.00
% 10.61/4.10  Index Deletion       : 0.00
% 10.61/4.10  Index Matching       : 0.00
% 10.61/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
