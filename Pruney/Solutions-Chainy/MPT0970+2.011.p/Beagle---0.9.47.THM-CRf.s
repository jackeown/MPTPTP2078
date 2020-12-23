%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:20 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 176 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 ( 455 expanded)
%              Number of equality atoms :   29 (  97 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_44,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1612,plain,(
    ! [A_248,B_249,C_250] :
      ( k2_relset_1(A_248,B_249,C_250) = k2_relat_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1621,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1612])).

tff(c_1622,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1621,c_44])).

tff(c_95,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_1148,plain,(
    ! [C_192,B_193,A_194] :
      ( v5_relat_1(C_192,B_193)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1157,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1148])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1123,plain,(
    ! [B_190,A_191] :
      ( r1_tarski(k2_relat_1(B_190),A_191)
      | ~ v5_relat_1(B_190,A_191)
      | ~ v1_relat_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    ! [B_60,A_61,A_62] :
      ( ~ v1_xboole_0(B_60)
      | ~ r2_hidden(A_61,A_62)
      | ~ r1_tarski(A_62,B_60) ) ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_133,plain,(
    ! [B_63,A_64,B_65] :
      ( ~ v1_xboole_0(B_63)
      | ~ r1_tarski(A_64,B_63)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_150,plain,(
    ! [B_69,B_70] :
      ( ~ v1_xboole_0(B_69)
      | r1_tarski(B_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_165,plain,(
    ! [B_70,B_69] :
      ( B_70 = B_69
      | ~ r1_tarski(B_70,B_69)
      | ~ v1_xboole_0(B_69) ) ),
    inference(resolution,[status(thm)],[c_150,c_18])).

tff(c_1539,plain,(
    ! [B_241,A_242] :
      ( k2_relat_1(B_241) = A_242
      | ~ v1_xboole_0(A_242)
      | ~ v5_relat_1(B_241,A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(resolution,[status(thm)],[c_1123,c_165])).

tff(c_1548,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ v1_xboole_0('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1157,c_1539])).

tff(c_1558,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1548])).

tff(c_1561,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1558])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_7'(D_34),'#skF_4')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_6','#skF_7'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2158,plain,(
    ! [D_307,C_308,A_309,B_310] :
      ( r2_hidden(k1_funct_1(D_307,C_308),k2_relset_1(A_309,B_310,D_307))
      | k1_xboole_0 = B_310
      | ~ r2_hidden(C_308,A_309)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_2(D_307,A_309,B_310)
      | ~ v1_funct_1(D_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2174,plain,(
    ! [D_34,A_309,B_310] :
      ( r2_hidden(D_34,k2_relset_1(A_309,B_310,'#skF_6'))
      | k1_xboole_0 = B_310
      | ~ r2_hidden('#skF_7'(D_34),A_309)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_2('#skF_6',A_309,B_310)
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2158])).

tff(c_2305,plain,(
    ! [D_319,A_320,B_321] :
      ( r2_hidden(D_319,k2_relset_1(A_320,B_321,'#skF_6'))
      | k1_xboole_0 = B_321
      | ~ r2_hidden('#skF_7'(D_319),A_320)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ v1_funct_2('#skF_6',A_320,B_321)
      | ~ r2_hidden(D_319,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2174])).

tff(c_2709,plain,(
    ! [D_346,B_347] :
      ( r2_hidden(D_346,k2_relset_1('#skF_4',B_347,'#skF_6'))
      | k1_xboole_0 = B_347
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_347)))
      | ~ v1_funct_2('#skF_6','#skF_4',B_347)
      | ~ r2_hidden(D_346,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_2305])).

tff(c_2714,plain,(
    ! [D_346] :
      ( r2_hidden(D_346,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ r2_hidden(D_346,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_2709])).

tff(c_2718,plain,(
    ! [D_346] :
      ( r2_hidden(D_346,k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(D_346,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1621,c_2714])).

tff(c_2719,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2718])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2740,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2719,c_8])).

tff(c_2742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1561,c_2740])).

tff(c_2745,plain,(
    ! [D_348] :
      ( r2_hidden(D_348,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_348,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2718])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2970,plain,(
    ! [A_365] :
      ( r1_tarski(A_365,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_365,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2745,c_4])).

tff(c_2980,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_2970])).

tff(c_1147,plain,(
    ! [B_190,A_191] :
      ( k2_relat_1(B_190) = A_191
      | ~ r1_tarski(A_191,k2_relat_1(B_190))
      | ~ v5_relat_1(B_190,A_191)
      | ~ v1_relat_1(B_190) ) ),
    inference(resolution,[status(thm)],[c_1123,c_18])).

tff(c_2988,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2980,c_1147])).

tff(c_3002,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1157,c_2988])).

tff(c_3004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1622,c_3002])).

tff(c_3005,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1558])).

tff(c_3026,plain,(
    ! [A_366,B_367,C_368] :
      ( k2_relset_1(A_366,B_367,C_368) = k2_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3035,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_3026])).

tff(c_3080,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3005,c_3035])).

tff(c_3081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.73  
% 4.20/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.20/1.73  
% 4.20/1.73  %Foreground sorts:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Background operators:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Foreground operators:
% 4.20/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.20/1.73  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.20/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.20/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.20/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.20/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.20/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.20/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.20/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.20/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.20/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.20/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.73  
% 4.20/1.74  tff(f_108, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.20/1.74  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.20/1.74  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.20/1.74  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.20/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.20/1.74  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.20/1.74  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.20/1.74  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.20/1.74  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.20/1.74  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 4.20/1.74  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.20/1.74  tff(c_44, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.74  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.74  tff(c_1612, plain, (![A_248, B_249, C_250]: (k2_relset_1(A_248, B_249, C_250)=k2_relat_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.20/1.74  tff(c_1621, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1612])).
% 4.20/1.74  tff(c_1622, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1621, c_44])).
% 4.20/1.74  tff(c_95, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.20/1.74  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_95])).
% 4.20/1.74  tff(c_1148, plain, (![C_192, B_193, A_194]: (v5_relat_1(C_192, B_193) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.20/1.74  tff(c_1157, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_1148])).
% 4.20/1.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.74  tff(c_1123, plain, (![B_190, A_191]: (r1_tarski(k2_relat_1(B_190), A_191) | ~v5_relat_1(B_190, A_191) | ~v1_relat_1(B_190))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.20/1.74  tff(c_22, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.20/1.74  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.20/1.74  tff(c_105, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.20/1.74  tff(c_126, plain, (![B_60, A_61, A_62]: (~v1_xboole_0(B_60) | ~r2_hidden(A_61, A_62) | ~r1_tarski(A_62, B_60))), inference(resolution, [status(thm)], [c_26, c_105])).
% 4.20/1.74  tff(c_133, plain, (![B_63, A_64, B_65]: (~v1_xboole_0(B_63) | ~r1_tarski(A_64, B_63) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_6, c_126])).
% 4.20/1.74  tff(c_150, plain, (![B_69, B_70]: (~v1_xboole_0(B_69) | r1_tarski(B_69, B_70))), inference(resolution, [status(thm)], [c_22, c_133])).
% 4.20/1.74  tff(c_18, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.20/1.74  tff(c_165, plain, (![B_70, B_69]: (B_70=B_69 | ~r1_tarski(B_70, B_69) | ~v1_xboole_0(B_69))), inference(resolution, [status(thm)], [c_150, c_18])).
% 4.20/1.74  tff(c_1539, plain, (![B_241, A_242]: (k2_relat_1(B_241)=A_242 | ~v1_xboole_0(A_242) | ~v5_relat_1(B_241, A_242) | ~v1_relat_1(B_241))), inference(resolution, [status(thm)], [c_1123, c_165])).
% 4.20/1.74  tff(c_1548, plain, (k2_relat_1('#skF_6')='#skF_5' | ~v1_xboole_0('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1157, c_1539])).
% 4.20/1.74  tff(c_1558, plain, (k2_relat_1('#skF_6')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1548])).
% 4.20/1.74  tff(c_1561, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1558])).
% 4.20/1.74  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.74  tff(c_54, plain, (![D_34]: (r2_hidden('#skF_7'(D_34), '#skF_4') | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.74  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.74  tff(c_52, plain, (![D_34]: (k1_funct_1('#skF_6', '#skF_7'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.20/1.74  tff(c_2158, plain, (![D_307, C_308, A_309, B_310]: (r2_hidden(k1_funct_1(D_307, C_308), k2_relset_1(A_309, B_310, D_307)) | k1_xboole_0=B_310 | ~r2_hidden(C_308, A_309) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~v1_funct_2(D_307, A_309, B_310) | ~v1_funct_1(D_307))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.20/1.74  tff(c_2174, plain, (![D_34, A_309, B_310]: (r2_hidden(D_34, k2_relset_1(A_309, B_310, '#skF_6')) | k1_xboole_0=B_310 | ~r2_hidden('#skF_7'(D_34), A_309) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~v1_funct_2('#skF_6', A_309, B_310) | ~v1_funct_1('#skF_6') | ~r2_hidden(D_34, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2158])).
% 4.20/1.74  tff(c_2305, plain, (![D_319, A_320, B_321]: (r2_hidden(D_319, k2_relset_1(A_320, B_321, '#skF_6')) | k1_xboole_0=B_321 | ~r2_hidden('#skF_7'(D_319), A_320) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~v1_funct_2('#skF_6', A_320, B_321) | ~r2_hidden(D_319, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2174])).
% 4.20/1.74  tff(c_2709, plain, (![D_346, B_347]: (r2_hidden(D_346, k2_relset_1('#skF_4', B_347, '#skF_6')) | k1_xboole_0=B_347 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_347))) | ~v1_funct_2('#skF_6', '#skF_4', B_347) | ~r2_hidden(D_346, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_2305])).
% 4.20/1.74  tff(c_2714, plain, (![D_346]: (r2_hidden(D_346, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~r2_hidden(D_346, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_2709])).
% 4.20/1.74  tff(c_2718, plain, (![D_346]: (r2_hidden(D_346, k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(D_346, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1621, c_2714])).
% 4.20/1.74  tff(c_2719, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2718])).
% 4.20/1.74  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/1.74  tff(c_2740, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2719, c_8])).
% 4.48/1.74  tff(c_2742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1561, c_2740])).
% 4.48/1.74  tff(c_2745, plain, (![D_348]: (r2_hidden(D_348, k2_relat_1('#skF_6')) | ~r2_hidden(D_348, '#skF_5'))), inference(splitRight, [status(thm)], [c_2718])).
% 4.48/1.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.48/1.74  tff(c_2970, plain, (![A_365]: (r1_tarski(A_365, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_1'(A_365, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_2745, c_4])).
% 4.48/1.74  tff(c_2980, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_2970])).
% 4.48/1.74  tff(c_1147, plain, (![B_190, A_191]: (k2_relat_1(B_190)=A_191 | ~r1_tarski(A_191, k2_relat_1(B_190)) | ~v5_relat_1(B_190, A_191) | ~v1_relat_1(B_190))), inference(resolution, [status(thm)], [c_1123, c_18])).
% 4.48/1.74  tff(c_2988, plain, (k2_relat_1('#skF_6')='#skF_5' | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2980, c_1147])).
% 4.48/1.74  tff(c_3002, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1157, c_2988])).
% 4.48/1.74  tff(c_3004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1622, c_3002])).
% 4.48/1.74  tff(c_3005, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_1558])).
% 4.48/1.74  tff(c_3026, plain, (![A_366, B_367, C_368]: (k2_relset_1(A_366, B_367, C_368)=k2_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.48/1.74  tff(c_3035, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_3026])).
% 4.48/1.74  tff(c_3080, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3005, c_3035])).
% 4.48/1.74  tff(c_3081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3080])).
% 4.48/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.74  
% 4.48/1.74  Inference rules
% 4.48/1.74  ----------------------
% 4.48/1.74  #Ref     : 0
% 4.48/1.74  #Sup     : 601
% 4.48/1.74  #Fact    : 0
% 4.48/1.74  #Define  : 0
% 4.48/1.74  #Split   : 11
% 4.48/1.74  #Chain   : 0
% 4.48/1.74  #Close   : 0
% 4.48/1.74  
% 4.48/1.74  Ordering : KBO
% 4.48/1.74  
% 4.48/1.74  Simplification rules
% 4.48/1.74  ----------------------
% 4.48/1.74  #Subsume      : 136
% 4.48/1.74  #Demod        : 534
% 4.48/1.74  #Tautology    : 240
% 4.48/1.74  #SimpNegUnit  : 7
% 4.48/1.74  #BackRed      : 31
% 4.48/1.74  
% 4.48/1.74  #Partial instantiations: 0
% 4.48/1.74  #Strategies tried      : 1
% 4.48/1.74  
% 4.48/1.74  Timing (in seconds)
% 4.48/1.74  ----------------------
% 4.48/1.75  Preprocessing        : 0.32
% 4.48/1.75  Parsing              : 0.17
% 4.48/1.75  CNF conversion       : 0.02
% 4.48/1.75  Main loop            : 0.66
% 4.48/1.75  Inferencing          : 0.24
% 4.48/1.75  Reduction            : 0.21
% 4.48/1.75  Demodulation         : 0.15
% 4.48/1.75  BG Simplification    : 0.02
% 4.48/1.75  Subsumption          : 0.14
% 4.48/1.75  Abstraction          : 0.03
% 4.48/1.75  MUC search           : 0.00
% 4.48/1.75  Cooper               : 0.00
% 4.48/1.75  Total                : 1.01
% 4.48/1.75  Index Insertion      : 0.00
% 4.48/1.75  Index Deletion       : 0.00
% 4.48/1.75  Index Matching       : 0.00
% 4.48/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
