%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:09 EST 2020

% Result     : Theorem 17.25s
% Output     : CNFRefutation 17.38s
% Verified   : 
% Statistics : Number of formulae       :   75 (  99 expanded)
%              Number of leaves         :   44 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 177 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_112,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_114,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_155,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_159,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_114,c_155])).

tff(c_118,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_116,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_239,plain,(
    ! [A_227,B_228,C_229] :
      ( k1_relset_1(A_227,B_228,C_229) = k1_relat_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_243,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_114,c_239])).

tff(c_504,plain,(
    ! [B_292,A_293,C_294] :
      ( k1_xboole_0 = B_292
      | k1_relset_1(A_293,B_292,C_294) = A_293
      | ~ v1_funct_2(C_294,A_293,B_292)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_507,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_114,c_504])).

tff(c_510,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_243,c_507])).

tff(c_511,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_169,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_173,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_114,c_169])).

tff(c_377,plain,(
    ! [B_251,A_252] :
      ( r2_hidden(k1_funct_1(B_251,A_252),k2_relat_1(B_251))
      | ~ r2_hidden(A_252,k1_relat_1(B_251))
      | ~ v1_funct_1(B_251)
      | ~ v1_relat_1(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_84,plain,(
    ! [C_50,A_47,B_48] :
      ( r2_hidden(C_50,A_47)
      | ~ r2_hidden(C_50,k2_relat_1(B_48))
      | ~ v5_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16550,plain,(
    ! [B_45667,A_45668,A_45669] :
      ( r2_hidden(k1_funct_1(B_45667,A_45668),A_45669)
      | ~ v5_relat_1(B_45667,A_45669)
      | ~ r2_hidden(A_45668,k1_relat_1(B_45667))
      | ~ v1_funct_1(B_45667)
      | ~ v1_relat_1(B_45667) ) ),
    inference(resolution,[status(thm)],[c_377,c_84])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_21369,plain,(
    ! [B_56700,A_56701,A_56702] :
      ( k1_funct_1(B_56700,A_56701) = A_56702
      | ~ v5_relat_1(B_56700,k1_tarski(A_56702))
      | ~ r2_hidden(A_56701,k1_relat_1(B_56700))
      | ~ v1_funct_1(B_56700)
      | ~ v1_relat_1(B_56700) ) ),
    inference(resolution,[status(thm)],[c_16550,c_4])).

tff(c_21377,plain,(
    ! [A_56701] :
      ( k1_funct_1('#skF_8',A_56701) = '#skF_6'
      | ~ r2_hidden(A_56701,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_173,c_21369])).

tff(c_21381,plain,(
    ! [A_57111] :
      ( k1_funct_1('#skF_8',A_57111) = '#skF_6'
      | ~ r2_hidden(A_57111,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_118,c_511,c_21377])).

tff(c_21396,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_112,c_21381])).

tff(c_21403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_21396])).

tff(c_21404,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [B_72,A_73] :
      ( ~ r1_tarski(B_72,A_73)
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_143,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_21416,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_21404,c_143])).

tff(c_21428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_21416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:58:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.25/9.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.25/9.32  
% 17.25/9.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.25/9.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 17.25/9.33  
% 17.25/9.33  %Foreground sorts:
% 17.25/9.33  
% 17.25/9.33  
% 17.25/9.33  %Background operators:
% 17.25/9.33  
% 17.25/9.33  
% 17.25/9.33  %Foreground operators:
% 17.25/9.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.25/9.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.25/9.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.25/9.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.25/9.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.25/9.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.25/9.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.25/9.33  tff('#skF_7', type, '#skF_7': $i).
% 17.25/9.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.25/9.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.25/9.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.25/9.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.25/9.33  tff('#skF_5', type, '#skF_5': $i).
% 17.25/9.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.25/9.33  tff('#skF_6', type, '#skF_6': $i).
% 17.25/9.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.25/9.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.25/9.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 17.25/9.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.25/9.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.25/9.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.25/9.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 17.25/9.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.25/9.33  tff('#skF_8', type, '#skF_8': $i).
% 17.25/9.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.25/9.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.25/9.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.25/9.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.25/9.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.25/9.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.25/9.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.25/9.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.25/9.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.25/9.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.25/9.33  
% 17.38/9.34  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.38/9.34  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 17.38/9.34  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.38/9.34  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 17.38/9.34  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 17.38/9.34  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 17.38/9.34  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 17.38/9.34  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 17.38/9.34  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 17.38/9.34  tff(f_100, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 17.38/9.34  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.38/9.34  tff(c_110, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_143])).
% 17.38/9.34  tff(c_112, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 17.38/9.34  tff(c_114, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 17.38/9.34  tff(c_155, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 17.38/9.34  tff(c_159, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_114, c_155])).
% 17.38/9.34  tff(c_118, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_143])).
% 17.38/9.34  tff(c_116, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 17.38/9.34  tff(c_239, plain, (![A_227, B_228, C_229]: (k1_relset_1(A_227, B_228, C_229)=k1_relat_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.38/9.34  tff(c_243, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_114, c_239])).
% 17.38/9.34  tff(c_504, plain, (![B_292, A_293, C_294]: (k1_xboole_0=B_292 | k1_relset_1(A_293, B_292, C_294)=A_293 | ~v1_funct_2(C_294, A_293, B_292) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.38/9.34  tff(c_507, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_114, c_504])).
% 17.38/9.34  tff(c_510, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_243, c_507])).
% 17.38/9.34  tff(c_511, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_510])).
% 17.38/9.34  tff(c_169, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.38/9.34  tff(c_173, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_114, c_169])).
% 17.38/9.34  tff(c_377, plain, (![B_251, A_252]: (r2_hidden(k1_funct_1(B_251, A_252), k2_relat_1(B_251)) | ~r2_hidden(A_252, k1_relat_1(B_251)) | ~v1_funct_1(B_251) | ~v1_relat_1(B_251))), inference(cnfTransformation, [status(thm)], [f_95])).
% 17.38/9.34  tff(c_84, plain, (![C_50, A_47, B_48]: (r2_hidden(C_50, A_47) | ~r2_hidden(C_50, k2_relat_1(B_48)) | ~v5_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.38/9.34  tff(c_16550, plain, (![B_45667, A_45668, A_45669]: (r2_hidden(k1_funct_1(B_45667, A_45668), A_45669) | ~v5_relat_1(B_45667, A_45669) | ~r2_hidden(A_45668, k1_relat_1(B_45667)) | ~v1_funct_1(B_45667) | ~v1_relat_1(B_45667))), inference(resolution, [status(thm)], [c_377, c_84])).
% 17.38/9.34  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.38/9.34  tff(c_21369, plain, (![B_56700, A_56701, A_56702]: (k1_funct_1(B_56700, A_56701)=A_56702 | ~v5_relat_1(B_56700, k1_tarski(A_56702)) | ~r2_hidden(A_56701, k1_relat_1(B_56700)) | ~v1_funct_1(B_56700) | ~v1_relat_1(B_56700))), inference(resolution, [status(thm)], [c_16550, c_4])).
% 17.38/9.34  tff(c_21377, plain, (![A_56701]: (k1_funct_1('#skF_8', A_56701)='#skF_6' | ~r2_hidden(A_56701, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_173, c_21369])).
% 17.38/9.34  tff(c_21381, plain, (![A_57111]: (k1_funct_1('#skF_8', A_57111)='#skF_6' | ~r2_hidden(A_57111, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_118, c_511, c_21377])).
% 17.38/9.34  tff(c_21396, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_112, c_21381])).
% 17.38/9.34  tff(c_21403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_21396])).
% 17.38/9.34  tff(c_21404, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_510])).
% 17.38/9.34  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.38/9.34  tff(c_136, plain, (![B_72, A_73]: (~r1_tarski(B_72, A_73) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.38/9.34  tff(c_143, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_136])).
% 17.38/9.34  tff(c_21416, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_21404, c_143])).
% 17.38/9.34  tff(c_21428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_21416])).
% 17.38/9.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.38/9.34  
% 17.38/9.34  Inference rules
% 17.38/9.34  ----------------------
% 17.38/9.34  #Ref     : 0
% 17.38/9.34  #Sup     : 3858
% 17.38/9.34  #Fact    : 336
% 17.38/9.34  #Define  : 0
% 17.38/9.34  #Split   : 2
% 17.38/9.34  #Chain   : 0
% 17.38/9.34  #Close   : 0
% 17.38/9.34  
% 17.38/9.34  Ordering : KBO
% 17.38/9.34  
% 17.38/9.34  Simplification rules
% 17.38/9.34  ----------------------
% 17.38/9.34  #Subsume      : 2391
% 17.38/9.34  #Demod        : 53
% 17.38/9.34  #Tautology    : 394
% 17.38/9.34  #SimpNegUnit  : 1
% 17.38/9.34  #BackRed      : 5
% 17.38/9.34  
% 17.38/9.34  #Partial instantiations: 19182
% 17.38/9.34  #Strategies tried      : 1
% 17.38/9.34  
% 17.38/9.34  Timing (in seconds)
% 17.38/9.34  ----------------------
% 17.38/9.34  Preprocessing        : 0.45
% 17.38/9.34  Parsing              : 0.19
% 17.38/9.34  CNF conversion       : 0.03
% 17.38/9.34  Main loop            : 8.08
% 17.38/9.34  Inferencing          : 3.17
% 17.38/9.34  Reduction            : 1.33
% 17.38/9.34  Demodulation         : 1.07
% 17.38/9.34  BG Simplification    : 0.25
% 17.38/9.34  Subsumption          : 3.19
% 17.38/9.34  Abstraction          : 0.71
% 17.38/9.34  MUC search           : 0.00
% 17.38/9.34  Cooper               : 0.00
% 17.38/9.34  Total                : 8.56
% 17.38/9.35  Index Insertion      : 0.00
% 17.38/9.35  Index Deletion       : 0.00
% 17.38/9.35  Index Matching       : 0.00
% 17.38/9.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
