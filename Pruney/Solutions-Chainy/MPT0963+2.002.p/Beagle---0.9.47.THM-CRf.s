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
% DateTime   : Thu Dec  3 10:10:58 EST 2020

% Result     : Theorem 9.12s
% Output     : CNFRefutation 9.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 147 expanded)
%              Number of leaves         :   35 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 415 expanded)
%              Number of equality atoms :   10 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k1_relat_1(C) = A
            & ! [D] :
                ( r2_hidden(D,A)
               => r2_hidden(k1_funct_1(C,D),B) ) )
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_66,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_64,plain,(
    k1_relat_1('#skF_12') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7227,plain,(
    ! [B_443,A_444] :
      ( m1_subset_1(B_443,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_443),A_444)))
      | ~ r1_tarski(k2_relat_1(B_443),A_444)
      | ~ v1_funct_1(B_443)
      | ~ v1_relat_1(B_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7230,plain,(
    ! [A_444] :
      ( m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10',A_444)))
      | ~ r1_tarski(k2_relat_1('#skF_12'),A_444)
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_7227])).

tff(c_7233,plain,(
    ! [A_445] :
      ( m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10',A_445)))
      | ~ r1_tarski(k2_relat_1('#skF_12'),A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_7230])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11')))
    | ~ v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11')))
    | ~ v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60])).

tff(c_100,plain,(
    ~ v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_390,plain,(
    ! [A_112,C_113] :
      ( r2_hidden(k4_tarski('#skF_9'(A_112,k2_relat_1(A_112),C_113),C_113),A_112)
      | ~ r2_hidden(C_113,k2_relat_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_402,plain,(
    ! [A_114,C_115] :
      ( r2_hidden('#skF_9'(A_114,k2_relat_1(A_114),C_115),k1_relat_1(A_114))
      | ~ r2_hidden(C_115,k2_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_390,c_16])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,(
    ! [A_114,C_115,B_2] :
      ( r2_hidden('#skF_9'(A_114,k2_relat_1(A_114),C_115),B_2)
      | ~ r1_tarski(k1_relat_1(A_114),B_2)
      | ~ r2_hidden(C_115,k2_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_26,plain,(
    ! [A_27,C_42] :
      ( r2_hidden(k4_tarski('#skF_9'(A_27,k2_relat_1(A_27),C_42),C_42),A_27)
      | ~ r2_hidden(C_42,k2_relat_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_443,plain,(
    ! [C_121,A_122,B_123] :
      ( k1_funct_1(C_121,A_122) = B_123
      | ~ r2_hidden(k4_tarski(A_122,B_123),C_121)
      | ~ v1_funct_1(C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5287,plain,(
    ! [A_355,C_356] :
      ( k1_funct_1(A_355,'#skF_9'(A_355,k2_relat_1(A_355),C_356)) = C_356
      | ~ v1_funct_1(A_355)
      | ~ v1_relat_1(A_355)
      | ~ r2_hidden(C_356,k2_relat_1(A_355)) ) ),
    inference(resolution,[status(thm)],[c_26,c_443])).

tff(c_62,plain,(
    ! [D_60] :
      ( r2_hidden(k1_funct_1('#skF_12',D_60),'#skF_11')
      | ~ r2_hidden(D_60,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5316,plain,(
    ! [C_356] :
      ( r2_hidden(C_356,'#skF_11')
      | ~ r2_hidden('#skF_9'('#skF_12',k2_relat_1('#skF_12'),C_356),'#skF_10')
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(C_356,k2_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5287,c_62])).

tff(c_5604,plain,(
    ! [C_360] :
      ( r2_hidden(C_360,'#skF_11')
      | ~ r2_hidden('#skF_9'('#skF_12',k2_relat_1('#skF_12'),C_360),'#skF_10')
      | ~ r2_hidden(C_360,k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5316])).

tff(c_5616,plain,(
    ! [C_115] :
      ( r2_hidden(C_115,'#skF_11')
      | ~ r1_tarski(k1_relat_1('#skF_12'),'#skF_10')
      | ~ r2_hidden(C_115,k2_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_408,c_5604])).

tff(c_5647,plain,(
    ! [C_361] :
      ( r2_hidden(C_361,'#skF_11')
      | ~ r2_hidden(C_361,k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_64,c_5616])).

tff(c_6290,plain,(
    ! [B_372] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_12'),B_372),'#skF_11')
      | r1_tarski(k2_relat_1('#skF_12'),B_372) ) ),
    inference(resolution,[status(thm)],[c_6,c_5647])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6298,plain,(
    r1_tarski(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_6290,c_4])).

tff(c_341,plain,(
    ! [B_102,A_103] :
      ( v1_funct_2(B_102,k1_relat_1(B_102),A_103)
      | ~ r1_tarski(k2_relat_1(B_102),A_103)
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_344,plain,(
    ! [A_103] :
      ( v1_funct_2('#skF_12','#skF_10',A_103)
      | ~ r1_tarski(k2_relat_1('#skF_12'),A_103)
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_341])).

tff(c_346,plain,(
    ! [A_103] :
      ( v1_funct_2('#skF_12','#skF_10',A_103)
      | ~ r1_tarski(k2_relat_1('#skF_12'),A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_344])).

tff(c_6311,plain,(
    v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_6298,c_346])).

tff(c_6325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_6311])).

tff(c_6326,plain,(
    ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_7237,plain,(
    ~ r1_tarski(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_7233,c_6326])).

tff(c_6697,plain,(
    ! [A_414,C_415] :
      ( r2_hidden(k4_tarski('#skF_9'(A_414,k2_relat_1(A_414),C_415),C_415),A_414)
      | ~ r2_hidden(C_415,k2_relat_1(A_414)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6819,plain,(
    ! [A_419,C_420] :
      ( r2_hidden('#skF_9'(A_419,k2_relat_1(A_419),C_420),k1_relat_1(A_419))
      | ~ r2_hidden(C_420,k2_relat_1(A_419)) ) ),
    inference(resolution,[status(thm)],[c_6697,c_16])).

tff(c_6825,plain,(
    ! [A_419,C_420,B_2] :
      ( r2_hidden('#skF_9'(A_419,k2_relat_1(A_419),C_420),B_2)
      | ~ r1_tarski(k1_relat_1(A_419),B_2)
      | ~ r2_hidden(C_420,k2_relat_1(A_419)) ) ),
    inference(resolution,[status(thm)],[c_6819,c_2])).

tff(c_48,plain,(
    ! [C_53,A_51,B_52] :
      ( k1_funct_1(C_53,A_51) = B_52
      | ~ r2_hidden(k4_tarski(A_51,B_52),C_53)
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11790,plain,(
    ! [A_676,C_677] :
      ( k1_funct_1(A_676,'#skF_9'(A_676,k2_relat_1(A_676),C_677)) = C_677
      | ~ v1_funct_1(A_676)
      | ~ v1_relat_1(A_676)
      | ~ r2_hidden(C_677,k2_relat_1(A_676)) ) ),
    inference(resolution,[status(thm)],[c_6697,c_48])).

tff(c_11819,plain,(
    ! [C_677] :
      ( r2_hidden(C_677,'#skF_11')
      | ~ r2_hidden('#skF_9'('#skF_12',k2_relat_1('#skF_12'),C_677),'#skF_10')
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(C_677,k2_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11790,c_62])).

tff(c_12037,plain,(
    ! [C_680] :
      ( r2_hidden(C_680,'#skF_11')
      | ~ r2_hidden('#skF_9'('#skF_12',k2_relat_1('#skF_12'),C_680),'#skF_10')
      | ~ r2_hidden(C_680,k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_11819])).

tff(c_12045,plain,(
    ! [C_420] :
      ( r2_hidden(C_420,'#skF_11')
      | ~ r1_tarski(k1_relat_1('#skF_12'),'#skF_10')
      | ~ r2_hidden(C_420,k2_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_6825,c_12037])).

tff(c_12073,plain,(
    ! [C_681] :
      ( r2_hidden(C_681,'#skF_11')
      | ~ r2_hidden(C_681,k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_64,c_12045])).

tff(c_12932,plain,(
    ! [B_695] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_12'),B_695),'#skF_11')
      | r1_tarski(k2_relat_1('#skF_12'),B_695) ) ),
    inference(resolution,[status(thm)],[c_6,c_12073])).

tff(c_12938,plain,(
    r1_tarski(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_12932,c_4])).

tff(c_12943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7237,c_7237,c_12938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:54:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.12/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.12/3.02  
% 9.12/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.12/3.02  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 9.12/3.02  
% 9.12/3.02  %Foreground sorts:
% 9.12/3.02  
% 9.12/3.02  
% 9.12/3.02  %Background operators:
% 9.12/3.02  
% 9.12/3.02  
% 9.12/3.02  %Foreground operators:
% 9.12/3.02  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.12/3.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.12/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.12/3.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.12/3.02  tff('#skF_11', type, '#skF_11': $i).
% 9.12/3.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.12/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.12/3.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.12/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.12/3.02  tff('#skF_10', type, '#skF_10': $i).
% 9.12/3.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.12/3.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.12/3.02  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.12/3.02  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.12/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.12/3.02  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.12/3.02  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 9.12/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.12/3.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.12/3.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.12/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.12/3.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.12/3.02  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.12/3.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.12/3.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.12/3.02  tff('#skF_12', type, '#skF_12': $i).
% 9.12/3.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.12/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.12/3.02  
% 9.12/3.04  tff(f_120, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 9.12/3.04  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 9.12/3.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.12/3.04  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.12/3.04  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 9.12/3.04  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 9.12/3.04  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 9.12/3.04  tff(c_68, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.12/3.04  tff(c_66, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.12/3.04  tff(c_64, plain, (k1_relat_1('#skF_12')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.12/3.04  tff(c_7227, plain, (![B_443, A_444]: (m1_subset_1(B_443, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_443), A_444))) | ~r1_tarski(k2_relat_1(B_443), A_444) | ~v1_funct_1(B_443) | ~v1_relat_1(B_443))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.12/3.04  tff(c_7230, plain, (![A_444]: (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', A_444))) | ~r1_tarski(k2_relat_1('#skF_12'), A_444) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_7227])).
% 9.12/3.04  tff(c_7233, plain, (![A_445]: (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', A_445))) | ~r1_tarski(k2_relat_1('#skF_12'), A_445))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_7230])).
% 9.12/3.04  tff(c_60, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11'))) | ~v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.12/3.04  tff(c_70, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11'))) | ~v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60])).
% 9.12/3.04  tff(c_100, plain, (~v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_70])).
% 9.12/3.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.12/3.04  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.12/3.04  tff(c_390, plain, (![A_112, C_113]: (r2_hidden(k4_tarski('#skF_9'(A_112, k2_relat_1(A_112), C_113), C_113), A_112) | ~r2_hidden(C_113, k2_relat_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.12/3.04  tff(c_16, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.12/3.04  tff(c_402, plain, (![A_114, C_115]: (r2_hidden('#skF_9'(A_114, k2_relat_1(A_114), C_115), k1_relat_1(A_114)) | ~r2_hidden(C_115, k2_relat_1(A_114)))), inference(resolution, [status(thm)], [c_390, c_16])).
% 9.12/3.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.12/3.04  tff(c_408, plain, (![A_114, C_115, B_2]: (r2_hidden('#skF_9'(A_114, k2_relat_1(A_114), C_115), B_2) | ~r1_tarski(k1_relat_1(A_114), B_2) | ~r2_hidden(C_115, k2_relat_1(A_114)))), inference(resolution, [status(thm)], [c_402, c_2])).
% 9.12/3.04  tff(c_26, plain, (![A_27, C_42]: (r2_hidden(k4_tarski('#skF_9'(A_27, k2_relat_1(A_27), C_42), C_42), A_27) | ~r2_hidden(C_42, k2_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.12/3.04  tff(c_443, plain, (![C_121, A_122, B_123]: (k1_funct_1(C_121, A_122)=B_123 | ~r2_hidden(k4_tarski(A_122, B_123), C_121) | ~v1_funct_1(C_121) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.12/3.04  tff(c_5287, plain, (![A_355, C_356]: (k1_funct_1(A_355, '#skF_9'(A_355, k2_relat_1(A_355), C_356))=C_356 | ~v1_funct_1(A_355) | ~v1_relat_1(A_355) | ~r2_hidden(C_356, k2_relat_1(A_355)))), inference(resolution, [status(thm)], [c_26, c_443])).
% 9.12/3.04  tff(c_62, plain, (![D_60]: (r2_hidden(k1_funct_1('#skF_12', D_60), '#skF_11') | ~r2_hidden(D_60, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.12/3.04  tff(c_5316, plain, (![C_356]: (r2_hidden(C_356, '#skF_11') | ~r2_hidden('#skF_9'('#skF_12', k2_relat_1('#skF_12'), C_356), '#skF_10') | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(C_356, k2_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_5287, c_62])).
% 9.12/3.04  tff(c_5604, plain, (![C_360]: (r2_hidden(C_360, '#skF_11') | ~r2_hidden('#skF_9'('#skF_12', k2_relat_1('#skF_12'), C_360), '#skF_10') | ~r2_hidden(C_360, k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5316])).
% 9.12/3.04  tff(c_5616, plain, (![C_115]: (r2_hidden(C_115, '#skF_11') | ~r1_tarski(k1_relat_1('#skF_12'), '#skF_10') | ~r2_hidden(C_115, k2_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_408, c_5604])).
% 9.12/3.04  tff(c_5647, plain, (![C_361]: (r2_hidden(C_361, '#skF_11') | ~r2_hidden(C_361, k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_64, c_5616])).
% 9.12/3.04  tff(c_6290, plain, (![B_372]: (r2_hidden('#skF_1'(k2_relat_1('#skF_12'), B_372), '#skF_11') | r1_tarski(k2_relat_1('#skF_12'), B_372))), inference(resolution, [status(thm)], [c_6, c_5647])).
% 9.12/3.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.12/3.04  tff(c_6298, plain, (r1_tarski(k2_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_6290, c_4])).
% 9.12/3.04  tff(c_341, plain, (![B_102, A_103]: (v1_funct_2(B_102, k1_relat_1(B_102), A_103) | ~r1_tarski(k2_relat_1(B_102), A_103) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.12/3.04  tff(c_344, plain, (![A_103]: (v1_funct_2('#skF_12', '#skF_10', A_103) | ~r1_tarski(k2_relat_1('#skF_12'), A_103) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_341])).
% 9.12/3.04  tff(c_346, plain, (![A_103]: (v1_funct_2('#skF_12', '#skF_10', A_103) | ~r1_tarski(k2_relat_1('#skF_12'), A_103))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_344])).
% 9.12/3.04  tff(c_6311, plain, (v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_6298, c_346])).
% 9.12/3.04  tff(c_6325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_6311])).
% 9.12/3.04  tff(c_6326, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_70])).
% 9.12/3.04  tff(c_7237, plain, (~r1_tarski(k2_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_7233, c_6326])).
% 9.12/3.04  tff(c_6697, plain, (![A_414, C_415]: (r2_hidden(k4_tarski('#skF_9'(A_414, k2_relat_1(A_414), C_415), C_415), A_414) | ~r2_hidden(C_415, k2_relat_1(A_414)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.12/3.04  tff(c_6819, plain, (![A_419, C_420]: (r2_hidden('#skF_9'(A_419, k2_relat_1(A_419), C_420), k1_relat_1(A_419)) | ~r2_hidden(C_420, k2_relat_1(A_419)))), inference(resolution, [status(thm)], [c_6697, c_16])).
% 9.12/3.04  tff(c_6825, plain, (![A_419, C_420, B_2]: (r2_hidden('#skF_9'(A_419, k2_relat_1(A_419), C_420), B_2) | ~r1_tarski(k1_relat_1(A_419), B_2) | ~r2_hidden(C_420, k2_relat_1(A_419)))), inference(resolution, [status(thm)], [c_6819, c_2])).
% 9.12/3.04  tff(c_48, plain, (![C_53, A_51, B_52]: (k1_funct_1(C_53, A_51)=B_52 | ~r2_hidden(k4_tarski(A_51, B_52), C_53) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.12/3.04  tff(c_11790, plain, (![A_676, C_677]: (k1_funct_1(A_676, '#skF_9'(A_676, k2_relat_1(A_676), C_677))=C_677 | ~v1_funct_1(A_676) | ~v1_relat_1(A_676) | ~r2_hidden(C_677, k2_relat_1(A_676)))), inference(resolution, [status(thm)], [c_6697, c_48])).
% 9.12/3.04  tff(c_11819, plain, (![C_677]: (r2_hidden(C_677, '#skF_11') | ~r2_hidden('#skF_9'('#skF_12', k2_relat_1('#skF_12'), C_677), '#skF_10') | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(C_677, k2_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_11790, c_62])).
% 9.12/3.04  tff(c_12037, plain, (![C_680]: (r2_hidden(C_680, '#skF_11') | ~r2_hidden('#skF_9'('#skF_12', k2_relat_1('#skF_12'), C_680), '#skF_10') | ~r2_hidden(C_680, k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_11819])).
% 9.12/3.04  tff(c_12045, plain, (![C_420]: (r2_hidden(C_420, '#skF_11') | ~r1_tarski(k1_relat_1('#skF_12'), '#skF_10') | ~r2_hidden(C_420, k2_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_6825, c_12037])).
% 9.12/3.04  tff(c_12073, plain, (![C_681]: (r2_hidden(C_681, '#skF_11') | ~r2_hidden(C_681, k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_64, c_12045])).
% 9.12/3.04  tff(c_12932, plain, (![B_695]: (r2_hidden('#skF_1'(k2_relat_1('#skF_12'), B_695), '#skF_11') | r1_tarski(k2_relat_1('#skF_12'), B_695))), inference(resolution, [status(thm)], [c_6, c_12073])).
% 9.12/3.04  tff(c_12938, plain, (r1_tarski(k2_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_12932, c_4])).
% 9.12/3.04  tff(c_12943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7237, c_7237, c_12938])).
% 9.12/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.12/3.04  
% 9.12/3.04  Inference rules
% 9.12/3.04  ----------------------
% 9.12/3.04  #Ref     : 0
% 9.12/3.04  #Sup     : 2861
% 9.12/3.04  #Fact    : 2
% 9.12/3.04  #Define  : 0
% 9.12/3.04  #Split   : 27
% 9.12/3.04  #Chain   : 0
% 9.12/3.04  #Close   : 0
% 9.12/3.04  
% 9.12/3.04  Ordering : KBO
% 9.12/3.04  
% 9.12/3.04  Simplification rules
% 9.12/3.04  ----------------------
% 9.12/3.04  #Subsume      : 543
% 9.12/3.04  #Demod        : 1130
% 9.12/3.04  #Tautology    : 678
% 9.12/3.04  #SimpNegUnit  : 13
% 9.12/3.04  #BackRed      : 31
% 9.12/3.04  
% 9.12/3.04  #Partial instantiations: 0
% 9.12/3.04  #Strategies tried      : 1
% 9.12/3.04  
% 9.12/3.04  Timing (in seconds)
% 9.12/3.04  ----------------------
% 9.12/3.04  Preprocessing        : 0.32
% 9.12/3.04  Parsing              : 0.17
% 9.12/3.04  CNF conversion       : 0.03
% 9.12/3.04  Main loop            : 1.97
% 9.12/3.04  Inferencing          : 0.64
% 9.12/3.04  Reduction            : 0.52
% 9.12/3.04  Demodulation         : 0.32
% 9.12/3.04  BG Simplification    : 0.08
% 9.12/3.04  Subsumption          : 0.55
% 9.12/3.04  Abstraction          : 0.09
% 9.12/3.04  MUC search           : 0.00
% 9.12/3.04  Cooper               : 0.00
% 9.12/3.04  Total                : 2.32
% 9.12/3.04  Index Insertion      : 0.00
% 9.12/3.04  Index Deletion       : 0.00
% 9.12/3.04  Index Matching       : 0.00
% 9.12/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
