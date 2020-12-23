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
% DateTime   : Thu Dec  3 09:58:30 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 203 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_743,plain,(
    ! [A_193,C_194] :
      ( r2_hidden(k4_tarski('#skF_5'(A_193,k2_relat_1(A_193),C_194),C_194),A_193)
      | ~ r2_hidden(C_194,k2_relat_1(A_193)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3311,plain,(
    ! [A_351,C_352,B_353] :
      ( r2_hidden(k4_tarski('#skF_5'(A_351,k2_relat_1(A_351),C_352),C_352),B_353)
      | ~ r1_tarski(A_351,B_353)
      | ~ r2_hidden(C_352,k2_relat_1(A_351)) ) ),
    inference(resolution,[status(thm)],[c_743,c_2])).

tff(c_24,plain,(
    ! [C_36,A_21,D_39] :
      ( r2_hidden(C_36,k2_relat_1(A_21))
      | ~ r2_hidden(k4_tarski(D_39,C_36),A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4018,plain,(
    ! [C_398,B_399,A_400] :
      ( r2_hidden(C_398,k2_relat_1(B_399))
      | ~ r1_tarski(A_400,B_399)
      | ~ r2_hidden(C_398,k2_relat_1(A_400)) ) ),
    inference(resolution,[status(thm)],[c_3311,c_24])).

tff(c_4109,plain,(
    ! [C_401] :
      ( r2_hidden(C_401,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_401,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_46,c_4018])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4727,plain,(
    ! [A_427] :
      ( r1_tarski(A_427,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_427,k2_relat_1('#skF_7')),k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4109,c_4])).

tff(c_4737,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_4727])).

tff(c_48,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_106,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_1,B_2,B_71] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_71)
      | ~ r1_tarski(A_1,B_71)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_40,plain,(
    ! [B_45,C_46,A_44] :
      ( r2_hidden(B_45,k3_relat_1(C_46))
      | ~ r2_hidden(k4_tarski(A_44,B_45),C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_759,plain,(
    ! [C_195,A_196] :
      ( r2_hidden(C_195,k3_relat_1(A_196))
      | ~ v1_relat_1(A_196)
      | ~ r2_hidden(C_195,k2_relat_1(A_196)) ) ),
    inference(resolution,[status(thm)],[c_743,c_40])).

tff(c_4787,plain,(
    ! [A_428,A_429] :
      ( r1_tarski(A_428,k3_relat_1(A_429))
      | ~ v1_relat_1(A_429)
      | ~ r2_hidden('#skF_1'(A_428,k3_relat_1(A_429)),k2_relat_1(A_429)) ) ),
    inference(resolution,[status(thm)],[c_759,c_4])).

tff(c_5871,plain,(
    ! [A_477,A_478] :
      ( ~ v1_relat_1(A_477)
      | ~ r1_tarski(A_478,k2_relat_1(A_477))
      | r1_tarski(A_478,k3_relat_1(A_477)) ) ),
    inference(resolution,[status(thm)],[c_109,c_4787])).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    ! [A_41,B_43] :
      ( r1_tarski(k1_relat_1(A_41),k1_relat_1(B_43))
      | ~ r1_tarski(A_41,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    ! [A_85] :
      ( k2_xboole_0(k1_relat_1(A_85),k2_relat_1(A_85)) = k3_relat_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_175,plain,(
    ! [A_86] :
      ( r1_tarski(k1_relat_1(A_86),k3_relat_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_10])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_184,plain,(
    ! [A_6,A_86] :
      ( r1_tarski(A_6,k3_relat_1(A_86))
      | ~ r1_tarski(A_6,k1_relat_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_175,c_8])).

tff(c_34,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_187,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_tarski(k2_xboole_0(A_88,C_89),B_90)
      | ~ r1_tarski(C_89,B_90)
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2096,plain,(
    ! [A_297,B_298] :
      ( r1_tarski(k3_relat_1(A_297),B_298)
      | ~ r1_tarski(k2_relat_1(A_297),B_298)
      | ~ r1_tarski(k1_relat_1(A_297),B_298)
      | ~ v1_relat_1(A_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_187])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2162,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2096,c_44])).

tff(c_2188,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2162])).

tff(c_2189,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2188])).

tff(c_2192,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_184,c_2189])).

tff(c_2195,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2192])).

tff(c_2198,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_2195])).

tff(c_2202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_2198])).

tff(c_2203,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2188])).

tff(c_5945,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_5871,c_2203])).

tff(c_6021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4737,c_48,c_5945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:44:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.54  
% 7.23/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 7.23/2.55  
% 7.23/2.55  %Foreground sorts:
% 7.23/2.55  
% 7.23/2.55  
% 7.23/2.55  %Background operators:
% 7.23/2.55  
% 7.23/2.55  
% 7.23/2.55  %Foreground operators:
% 7.23/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.23/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.23/2.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.23/2.55  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.23/2.55  tff('#skF_7', type, '#skF_7': $i).
% 7.23/2.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.23/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.23/2.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.23/2.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.23/2.55  tff('#skF_6', type, '#skF_6': $i).
% 7.23/2.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.23/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.23/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.23/2.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.23/2.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.23/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.23/2.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.23/2.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.23/2.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.23/2.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.23/2.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.23/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.23/2.55  
% 7.51/2.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.51/2.56  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 7.51/2.56  tff(f_67, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 7.51/2.56  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 7.51/2.56  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 7.51/2.56  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.51/2.56  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.51/2.56  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.51/2.56  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.51/2.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.51/2.56  tff(c_46, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.51/2.56  tff(c_743, plain, (![A_193, C_194]: (r2_hidden(k4_tarski('#skF_5'(A_193, k2_relat_1(A_193), C_194), C_194), A_193) | ~r2_hidden(C_194, k2_relat_1(A_193)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.51/2.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.51/2.56  tff(c_3311, plain, (![A_351, C_352, B_353]: (r2_hidden(k4_tarski('#skF_5'(A_351, k2_relat_1(A_351), C_352), C_352), B_353) | ~r1_tarski(A_351, B_353) | ~r2_hidden(C_352, k2_relat_1(A_351)))), inference(resolution, [status(thm)], [c_743, c_2])).
% 7.51/2.56  tff(c_24, plain, (![C_36, A_21, D_39]: (r2_hidden(C_36, k2_relat_1(A_21)) | ~r2_hidden(k4_tarski(D_39, C_36), A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.51/2.56  tff(c_4018, plain, (![C_398, B_399, A_400]: (r2_hidden(C_398, k2_relat_1(B_399)) | ~r1_tarski(A_400, B_399) | ~r2_hidden(C_398, k2_relat_1(A_400)))), inference(resolution, [status(thm)], [c_3311, c_24])).
% 7.51/2.56  tff(c_4109, plain, (![C_401]: (r2_hidden(C_401, k2_relat_1('#skF_7')) | ~r2_hidden(C_401, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_46, c_4018])).
% 7.51/2.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.51/2.56  tff(c_4727, plain, (![A_427]: (r1_tarski(A_427, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_427, k2_relat_1('#skF_7')), k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_4109, c_4])).
% 7.51/2.56  tff(c_4737, plain, (r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_4727])).
% 7.51/2.56  tff(c_48, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.51/2.56  tff(c_106, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.51/2.56  tff(c_109, plain, (![A_1, B_2, B_71]: (r2_hidden('#skF_1'(A_1, B_2), B_71) | ~r1_tarski(A_1, B_71) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_106])).
% 7.51/2.56  tff(c_40, plain, (![B_45, C_46, A_44]: (r2_hidden(B_45, k3_relat_1(C_46)) | ~r2_hidden(k4_tarski(A_44, B_45), C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.51/2.56  tff(c_759, plain, (![C_195, A_196]: (r2_hidden(C_195, k3_relat_1(A_196)) | ~v1_relat_1(A_196) | ~r2_hidden(C_195, k2_relat_1(A_196)))), inference(resolution, [status(thm)], [c_743, c_40])).
% 7.51/2.56  tff(c_4787, plain, (![A_428, A_429]: (r1_tarski(A_428, k3_relat_1(A_429)) | ~v1_relat_1(A_429) | ~r2_hidden('#skF_1'(A_428, k3_relat_1(A_429)), k2_relat_1(A_429)))), inference(resolution, [status(thm)], [c_759, c_4])).
% 7.51/2.56  tff(c_5871, plain, (![A_477, A_478]: (~v1_relat_1(A_477) | ~r1_tarski(A_478, k2_relat_1(A_477)) | r1_tarski(A_478, k3_relat_1(A_477)))), inference(resolution, [status(thm)], [c_109, c_4787])).
% 7.51/2.56  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.51/2.56  tff(c_38, plain, (![A_41, B_43]: (r1_tarski(k1_relat_1(A_41), k1_relat_1(B_43)) | ~r1_tarski(A_41, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.51/2.56  tff(c_154, plain, (![A_85]: (k2_xboole_0(k1_relat_1(A_85), k2_relat_1(A_85))=k3_relat_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.51/2.56  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.51/2.56  tff(c_175, plain, (![A_86]: (r1_tarski(k1_relat_1(A_86), k3_relat_1(A_86)) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_154, c_10])).
% 7.51/2.56  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.51/2.56  tff(c_184, plain, (![A_6, A_86]: (r1_tarski(A_6, k3_relat_1(A_86)) | ~r1_tarski(A_6, k1_relat_1(A_86)) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_175, c_8])).
% 7.51/2.56  tff(c_34, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.51/2.56  tff(c_187, plain, (![A_88, C_89, B_90]: (r1_tarski(k2_xboole_0(A_88, C_89), B_90) | ~r1_tarski(C_89, B_90) | ~r1_tarski(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.51/2.56  tff(c_2096, plain, (![A_297, B_298]: (r1_tarski(k3_relat_1(A_297), B_298) | ~r1_tarski(k2_relat_1(A_297), B_298) | ~r1_tarski(k1_relat_1(A_297), B_298) | ~v1_relat_1(A_297))), inference(superposition, [status(thm), theory('equality')], [c_34, c_187])).
% 7.51/2.56  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.51/2.56  tff(c_2162, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2096, c_44])).
% 7.51/2.56  tff(c_2188, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2162])).
% 7.51/2.56  tff(c_2189, plain, (~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_2188])).
% 7.51/2.56  tff(c_2192, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_184, c_2189])).
% 7.51/2.56  tff(c_2195, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2192])).
% 7.51/2.56  tff(c_2198, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_2195])).
% 7.51/2.56  tff(c_2202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_2198])).
% 7.51/2.56  tff(c_2203, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_2188])).
% 7.51/2.56  tff(c_5945, plain, (~v1_relat_1('#skF_7') | ~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_5871, c_2203])).
% 7.51/2.56  tff(c_6021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4737, c_48, c_5945])).
% 7.51/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.56  
% 7.51/2.56  Inference rules
% 7.51/2.56  ----------------------
% 7.51/2.56  #Ref     : 0
% 7.51/2.56  #Sup     : 1425
% 7.51/2.56  #Fact    : 0
% 7.51/2.56  #Define  : 0
% 7.51/2.56  #Split   : 20
% 7.51/2.56  #Chain   : 0
% 7.51/2.56  #Close   : 0
% 7.51/2.56  
% 7.51/2.56  Ordering : KBO
% 7.51/2.56  
% 7.51/2.56  Simplification rules
% 7.51/2.56  ----------------------
% 7.51/2.56  #Subsume      : 500
% 7.51/2.56  #Demod        : 139
% 7.51/2.56  #Tautology    : 63
% 7.51/2.56  #SimpNegUnit  : 1
% 7.51/2.56  #BackRed      : 0
% 7.51/2.56  
% 7.51/2.56  #Partial instantiations: 0
% 7.53/2.56  #Strategies tried      : 1
% 7.53/2.56  
% 7.53/2.56  Timing (in seconds)
% 7.53/2.56  ----------------------
% 7.53/2.57  Preprocessing        : 0.33
% 7.53/2.57  Parsing              : 0.18
% 7.53/2.57  CNF conversion       : 0.03
% 7.53/2.57  Main loop            : 1.43
% 7.53/2.57  Inferencing          : 0.42
% 7.53/2.57  Reduction            : 0.37
% 7.53/2.57  Demodulation         : 0.24
% 7.53/2.57  BG Simplification    : 0.05
% 7.53/2.57  Subsumption          : 0.47
% 7.53/2.57  Abstraction          : 0.05
% 7.53/2.57  MUC search           : 0.00
% 7.53/2.57  Cooper               : 0.00
% 7.53/2.57  Total                : 1.79
% 7.53/2.57  Index Insertion      : 0.00
% 7.53/2.57  Index Deletion       : 0.00
% 7.53/2.57  Index Matching       : 0.00
% 7.53/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
