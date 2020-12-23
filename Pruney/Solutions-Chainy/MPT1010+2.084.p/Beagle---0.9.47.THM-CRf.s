%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   82 (  92 expanded)
%              Number of leaves         :   47 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 141 expanded)
%              Number of equality atoms :   47 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(c_60,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_144,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_148,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_144])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_38] : k1_setfam_1(k1_tarski(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_68,B_69] : k1_setfam_1(k2_tarski(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_122])).

tff(c_134,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_131])).

tff(c_149,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_158,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_149])).

tff(c_161,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_158])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_20])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_219,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_223,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_219])).

tff(c_276,plain,(
    ! [B_126,A_127,C_128] :
      ( k1_xboole_0 = B_126
      | k1_relset_1(A_127,B_126,C_128) = A_127
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_279,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_276])).

tff(c_282,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_223,c_279])).

tff(c_283,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_282])).

tff(c_46,plain,(
    ! [A_53,B_54] : k2_mcart_1(k4_tarski(A_53,B_54)) = B_54 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_249,plain,(
    ! [A_120,C_121] :
      ( r2_hidden(k4_tarski(A_120,k1_funct_1(C_121,A_120)),C_121)
      | ~ r2_hidden(A_120,k1_relat_1(C_121))
      | ~ v1_funct_1(C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_37,A_34,B_35] :
      ( r2_hidden(C_37,A_34)
      | ~ r2_hidden(C_37,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_310,plain,(
    ! [A_139,C_140,A_141] :
      ( r2_hidden(k4_tarski(A_139,k1_funct_1(C_140,A_139)),A_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(A_141))
      | ~ r2_hidden(A_139,k1_relat_1(C_140))
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_249,c_24])).

tff(c_40,plain,(
    ! [A_50,C_52,B_51] :
      ( k2_mcart_1(A_50) = C_52
      | ~ r2_hidden(A_50,k2_zfmisc_1(B_51,k1_tarski(C_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_326,plain,(
    ! [A_139,C_140,C_52,B_51] :
      ( k2_mcart_1(k4_tarski(A_139,k1_funct_1(C_140,A_139))) = C_52
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(B_51,k1_tarski(C_52))))
      | ~ r2_hidden(A_139,k1_relat_1(C_140))
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_310,c_40])).

tff(c_340,plain,(
    ! [C_146,A_147,C_148,B_149] :
      ( k1_funct_1(C_146,A_147) = C_148
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(B_149,k1_tarski(C_148))))
      | ~ r2_hidden(A_147,k1_relat_1(C_146))
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_326])).

tff(c_342,plain,(
    ! [A_147] :
      ( k1_funct_1('#skF_4',A_147) = '#skF_2'
      | ~ r2_hidden(A_147,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_340])).

tff(c_357,plain,(
    ! [A_153] :
      ( k1_funct_1('#skF_4',A_153) = '#skF_2'
      | ~ r2_hidden(A_153,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_68,c_283,c_342])).

tff(c_368,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_357])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:14:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.22  
% 2.31/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.23  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.23  
% 2.31/1.23  %Foreground sorts:
% 2.31/1.23  
% 2.31/1.23  
% 2.31/1.23  %Background operators:
% 2.31/1.23  
% 2.31/1.23  
% 2.31/1.23  %Foreground operators:
% 2.31/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.31/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.31/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.31/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.31/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.31/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.23  
% 2.46/1.24  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.46/1.24  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.24  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.46/1.24  tff(f_57, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.46/1.24  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.24  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.46/1.24  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.46/1.24  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.46/1.24  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.24  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.24  tff(f_87, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.46/1.24  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.46/1.24  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.46/1.24  tff(f_83, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.46/1.24  tff(c_60, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.24  tff(c_62, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.24  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.24  tff(c_144, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.24  tff(c_148, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_144])).
% 2.46/1.24  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.24  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.24  tff(c_26, plain, (![A_38]: (k1_setfam_1(k1_tarski(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.24  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.24  tff(c_122, plain, (![A_68, B_69]: (k1_setfam_1(k2_tarski(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.46/1.24  tff(c_131, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_122])).
% 2.46/1.24  tff(c_134, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_131])).
% 2.46/1.24  tff(c_149, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.24  tff(c_158, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_134, c_149])).
% 2.46/1.24  tff(c_161, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_158])).
% 2.46/1.24  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.24  tff(c_162, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_20])).
% 2.46/1.24  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.24  tff(c_219, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.24  tff(c_223, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_219])).
% 2.46/1.24  tff(c_276, plain, (![B_126, A_127, C_128]: (k1_xboole_0=B_126 | k1_relset_1(A_127, B_126, C_128)=A_127 | ~v1_funct_2(C_128, A_127, B_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.46/1.24  tff(c_279, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_276])).
% 2.46/1.24  tff(c_282, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_223, c_279])).
% 2.46/1.24  tff(c_283, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_162, c_282])).
% 2.46/1.24  tff(c_46, plain, (![A_53, B_54]: (k2_mcart_1(k4_tarski(A_53, B_54))=B_54)), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.24  tff(c_249, plain, (![A_120, C_121]: (r2_hidden(k4_tarski(A_120, k1_funct_1(C_121, A_120)), C_121) | ~r2_hidden(A_120, k1_relat_1(C_121)) | ~v1_funct_1(C_121) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.24  tff(c_24, plain, (![C_37, A_34, B_35]: (r2_hidden(C_37, A_34) | ~r2_hidden(C_37, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.24  tff(c_310, plain, (![A_139, C_140, A_141]: (r2_hidden(k4_tarski(A_139, k1_funct_1(C_140, A_139)), A_141) | ~m1_subset_1(C_140, k1_zfmisc_1(A_141)) | ~r2_hidden(A_139, k1_relat_1(C_140)) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140))), inference(resolution, [status(thm)], [c_249, c_24])).
% 2.46/1.24  tff(c_40, plain, (![A_50, C_52, B_51]: (k2_mcart_1(A_50)=C_52 | ~r2_hidden(A_50, k2_zfmisc_1(B_51, k1_tarski(C_52))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.46/1.24  tff(c_326, plain, (![A_139, C_140, C_52, B_51]: (k2_mcart_1(k4_tarski(A_139, k1_funct_1(C_140, A_139)))=C_52 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(B_51, k1_tarski(C_52)))) | ~r2_hidden(A_139, k1_relat_1(C_140)) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140))), inference(resolution, [status(thm)], [c_310, c_40])).
% 2.46/1.24  tff(c_340, plain, (![C_146, A_147, C_148, B_149]: (k1_funct_1(C_146, A_147)=C_148 | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(B_149, k1_tarski(C_148)))) | ~r2_hidden(A_147, k1_relat_1(C_146)) | ~v1_funct_1(C_146) | ~v1_relat_1(C_146))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_326])).
% 2.46/1.24  tff(c_342, plain, (![A_147]: (k1_funct_1('#skF_4', A_147)='#skF_2' | ~r2_hidden(A_147, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_340])).
% 2.46/1.24  tff(c_357, plain, (![A_153]: (k1_funct_1('#skF_4', A_153)='#skF_2' | ~r2_hidden(A_153, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_68, c_283, c_342])).
% 2.46/1.24  tff(c_368, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_62, c_357])).
% 2.46/1.24  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_368])).
% 2.46/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.24  
% 2.46/1.24  Inference rules
% 2.46/1.24  ----------------------
% 2.46/1.24  #Ref     : 0
% 2.46/1.24  #Sup     : 64
% 2.46/1.24  #Fact    : 0
% 2.46/1.24  #Define  : 0
% 2.46/1.24  #Split   : 0
% 2.46/1.24  #Chain   : 0
% 2.46/1.24  #Close   : 0
% 2.46/1.24  
% 2.46/1.24  Ordering : KBO
% 2.46/1.24  
% 2.46/1.24  Simplification rules
% 2.46/1.24  ----------------------
% 2.46/1.24  #Subsume      : 0
% 2.46/1.24  #Demod        : 18
% 2.46/1.24  #Tautology    : 44
% 2.46/1.24  #SimpNegUnit  : 5
% 2.46/1.24  #BackRed      : 2
% 2.46/1.24  
% 2.46/1.24  #Partial instantiations: 0
% 2.46/1.24  #Strategies tried      : 1
% 2.46/1.24  
% 2.46/1.24  Timing (in seconds)
% 2.46/1.24  ----------------------
% 2.46/1.24  Preprocessing        : 0.35
% 2.46/1.25  Parsing              : 0.19
% 2.46/1.25  CNF conversion       : 0.02
% 2.46/1.25  Main loop            : 0.22
% 2.46/1.25  Inferencing          : 0.08
% 2.46/1.25  Reduction            : 0.07
% 2.46/1.25  Demodulation         : 0.05
% 2.46/1.25  BG Simplification    : 0.02
% 2.46/1.25  Subsumption          : 0.03
% 2.46/1.25  Abstraction          : 0.01
% 2.46/1.25  MUC search           : 0.00
% 2.46/1.25  Cooper               : 0.00
% 2.46/1.25  Total                : 0.60
% 2.46/1.25  Index Insertion      : 0.00
% 2.46/1.25  Index Deletion       : 0.00
% 2.46/1.25  Index Matching       : 0.00
% 2.46/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
