%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 116 expanded)
%              Number of leaves         :   48 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 205 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_13 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    k1_funct_1('#skF_13','#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_96,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_100,plain,(
    v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_98,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_513,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_517,plain,(
    k1_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_513])).

tff(c_2077,plain,(
    ! [B_328,A_329,C_330] :
      ( k1_xboole_0 = B_328
      | k1_relset_1(A_329,B_328,C_330) = A_329
      | ~ v1_funct_2(C_330,A_329,B_328)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_329,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2084,plain,
    ( k1_tarski('#skF_11') = k1_xboole_0
    | k1_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = '#skF_10'
    | ~ v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_98,c_2077])).

tff(c_2088,plain,
    ( k1_tarski('#skF_11') = k1_xboole_0
    | k1_relat_1('#skF_13') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_517,c_2084])).

tff(c_2089,plain,(
    k1_relat_1('#skF_13') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_2088])).

tff(c_294,plain,(
    ! [C_135,A_136,B_137] :
      ( v1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_298,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_294])).

tff(c_102,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_681,plain,(
    ! [A_191,D_192] :
      ( r2_hidden(k1_funct_1(A_191,D_192),k2_relat_1(A_191))
      | ~ r2_hidden(D_192,k1_relat_1(A_191))
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_327,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_331,plain,(
    k2_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_327])).

tff(c_633,plain,(
    ! [A_187,B_188,C_189] :
      ( m1_subset_1(k2_relset_1(A_187,B_188,C_189),k1_zfmisc_1(B_188))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_650,plain,
    ( m1_subset_1(k2_relat_1('#skF_13'),k1_zfmisc_1(k1_tarski('#skF_11')))
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_633])).

tff(c_656,plain,(
    m1_subset_1(k2_relat_1('#skF_13'),k1_zfmisc_1(k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_650])).

tff(c_52,plain,(
    ! [A_26,C_28,B_27] :
      ( m1_subset_1(A_26,C_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(C_28))
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_659,plain,(
    ! [A_26] :
      ( m1_subset_1(A_26,k1_tarski('#skF_11'))
      | ~ r2_hidden(A_26,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_656,c_52])).

tff(c_685,plain,(
    ! [D_192] :
      ( m1_subset_1(k1_funct_1('#skF_13',D_192),k1_tarski('#skF_11'))
      | ~ r2_hidden(D_192,k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_681,c_659])).

tff(c_1431,plain,(
    ! [D_264] :
      ( m1_subset_1(k1_funct_1('#skF_13',D_264),k1_tarski('#skF_11'))
      | ~ r2_hidden(D_264,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_102,c_685])).

tff(c_34,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,(
    ! [B_88,A_89] :
      ( ~ r2_hidden(B_88,A_89)
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_256,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(A_127,B_128)
      | v1_xboole_0(B_128)
      | ~ m1_subset_1(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_263,plain,(
    ! [A_13,A_127] :
      ( A_13 = A_127
      | v1_xboole_0(k1_tarski(A_13))
      | ~ m1_subset_1(A_127,k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_256,c_32])).

tff(c_270,plain,(
    ! [A_13,A_127] :
      ( A_13 = A_127
      | ~ m1_subset_1(A_127,k1_tarski(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_263])).

tff(c_1435,plain,(
    ! [D_264] :
      ( k1_funct_1('#skF_13',D_264) = '#skF_11'
      | ~ r2_hidden(D_264,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_1431,c_270])).

tff(c_2129,plain,(
    ! [D_332] :
      ( k1_funct_1('#skF_13',D_332) = '#skF_11'
      | ~ r2_hidden(D_332,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_1435])).

tff(c_2148,plain,(
    k1_funct_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_96,c_2129])).

tff(c_2160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2148])).

tff(c_2161,plain,(
    k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2088])).

tff(c_146,plain,(
    ! [B_106,A_107] :
      ( ~ r1_tarski(B_106,A_107)
      | ~ r2_hidden(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_165,plain,(
    ! [C_17] : ~ r1_tarski(k1_tarski(C_17),C_17) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_2189,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_2161,c_165])).

tff(c_2203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.73  
% 4.26/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_13 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_12 > #skF_4
% 4.26/1.73  
% 4.26/1.73  %Foreground sorts:
% 4.26/1.73  
% 4.26/1.73  
% 4.26/1.73  %Background operators:
% 4.26/1.73  
% 4.26/1.73  
% 4.26/1.73  %Foreground operators:
% 4.26/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.26/1.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.26/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.26/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.73  tff('#skF_11', type, '#skF_11': $i).
% 4.26/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.26/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.26/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.26/1.73  tff('#skF_10', type, '#skF_10': $i).
% 4.26/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.26/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.26/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.26/1.73  tff('#skF_13', type, '#skF_13': $i).
% 4.26/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.26/1.73  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.26/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.26/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.26/1.73  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.26/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.26/1.73  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.26/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.26/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.26/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.73  tff('#skF_12', type, '#skF_12': $i).
% 4.26/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.26/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.73  
% 4.26/1.74  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.26/1.74  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.26/1.74  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.26/1.74  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.26/1.74  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.26/1.74  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.26/1.74  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.26/1.74  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.26/1.74  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.26/1.74  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.26/1.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.26/1.74  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.26/1.74  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.26/1.74  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.26/1.74  tff(c_94, plain, (k1_funct_1('#skF_13', '#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.26/1.74  tff(c_96, plain, (r2_hidden('#skF_12', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.26/1.74  tff(c_100, plain, (v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.26/1.74  tff(c_98, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.26/1.74  tff(c_513, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.26/1.74  tff(c_517, plain, (k1_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_98, c_513])).
% 4.26/1.74  tff(c_2077, plain, (![B_328, A_329, C_330]: (k1_xboole_0=B_328 | k1_relset_1(A_329, B_328, C_330)=A_329 | ~v1_funct_2(C_330, A_329, B_328) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_329, B_328))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.26/1.74  tff(c_2084, plain, (k1_tarski('#skF_11')=k1_xboole_0 | k1_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')='#skF_10' | ~v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_98, c_2077])).
% 4.26/1.74  tff(c_2088, plain, (k1_tarski('#skF_11')=k1_xboole_0 | k1_relat_1('#skF_13')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_517, c_2084])).
% 4.26/1.74  tff(c_2089, plain, (k1_relat_1('#skF_13')='#skF_10'), inference(splitLeft, [status(thm)], [c_2088])).
% 4.26/1.74  tff(c_294, plain, (![C_135, A_136, B_137]: (v1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.26/1.74  tff(c_298, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_98, c_294])).
% 4.26/1.74  tff(c_102, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.26/1.74  tff(c_681, plain, (![A_191, D_192]: (r2_hidden(k1_funct_1(A_191, D_192), k2_relat_1(A_191)) | ~r2_hidden(D_192, k1_relat_1(A_191)) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.26/1.74  tff(c_327, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.26/1.74  tff(c_331, plain, (k2_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_98, c_327])).
% 4.26/1.74  tff(c_633, plain, (![A_187, B_188, C_189]: (m1_subset_1(k2_relset_1(A_187, B_188, C_189), k1_zfmisc_1(B_188)) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.26/1.74  tff(c_650, plain, (m1_subset_1(k2_relat_1('#skF_13'), k1_zfmisc_1(k1_tarski('#skF_11'))) | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(superposition, [status(thm), theory('equality')], [c_331, c_633])).
% 4.26/1.74  tff(c_656, plain, (m1_subset_1(k2_relat_1('#skF_13'), k1_zfmisc_1(k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_650])).
% 4.26/1.74  tff(c_52, plain, (![A_26, C_28, B_27]: (m1_subset_1(A_26, C_28) | ~m1_subset_1(B_27, k1_zfmisc_1(C_28)) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.26/1.74  tff(c_659, plain, (![A_26]: (m1_subset_1(A_26, k1_tarski('#skF_11')) | ~r2_hidden(A_26, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_656, c_52])).
% 4.26/1.74  tff(c_685, plain, (![D_192]: (m1_subset_1(k1_funct_1('#skF_13', D_192), k1_tarski('#skF_11')) | ~r2_hidden(D_192, k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_681, c_659])).
% 4.26/1.74  tff(c_1431, plain, (![D_264]: (m1_subset_1(k1_funct_1('#skF_13', D_264), k1_tarski('#skF_11')) | ~r2_hidden(D_264, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_102, c_685])).
% 4.26/1.74  tff(c_34, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.26/1.74  tff(c_105, plain, (![B_88, A_89]: (~r2_hidden(B_88, A_89) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.74  tff(c_112, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_34, c_105])).
% 4.26/1.74  tff(c_256, plain, (![A_127, B_128]: (r2_hidden(A_127, B_128) | v1_xboole_0(B_128) | ~m1_subset_1(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.26/1.74  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.26/1.74  tff(c_263, plain, (![A_13, A_127]: (A_13=A_127 | v1_xboole_0(k1_tarski(A_13)) | ~m1_subset_1(A_127, k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_256, c_32])).
% 4.26/1.74  tff(c_270, plain, (![A_13, A_127]: (A_13=A_127 | ~m1_subset_1(A_127, k1_tarski(A_13)))), inference(negUnitSimplification, [status(thm)], [c_112, c_263])).
% 4.26/1.74  tff(c_1435, plain, (![D_264]: (k1_funct_1('#skF_13', D_264)='#skF_11' | ~r2_hidden(D_264, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_1431, c_270])).
% 4.26/1.74  tff(c_2129, plain, (![D_332]: (k1_funct_1('#skF_13', D_332)='#skF_11' | ~r2_hidden(D_332, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_1435])).
% 4.26/1.74  tff(c_2148, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_96, c_2129])).
% 4.26/1.74  tff(c_2160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_2148])).
% 4.26/1.74  tff(c_2161, plain, (k1_tarski('#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2088])).
% 4.26/1.74  tff(c_146, plain, (![B_106, A_107]: (~r1_tarski(B_106, A_107) | ~r2_hidden(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.26/1.74  tff(c_165, plain, (![C_17]: (~r1_tarski(k1_tarski(C_17), C_17))), inference(resolution, [status(thm)], [c_34, c_146])).
% 4.26/1.74  tff(c_2189, plain, (~r1_tarski(k1_xboole_0, '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_2161, c_165])).
% 4.26/1.74  tff(c_2203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2189])).
% 4.26/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.74  
% 4.26/1.74  Inference rules
% 4.26/1.74  ----------------------
% 4.26/1.74  #Ref     : 0
% 4.26/1.74  #Sup     : 430
% 4.26/1.74  #Fact    : 2
% 4.26/1.74  #Define  : 0
% 4.26/1.74  #Split   : 10
% 4.26/1.74  #Chain   : 0
% 4.26/1.74  #Close   : 0
% 4.26/1.74  
% 4.26/1.74  Ordering : KBO
% 4.26/1.74  
% 4.26/1.74  Simplification rules
% 4.26/1.74  ----------------------
% 4.26/1.74  #Subsume      : 97
% 4.26/1.74  #Demod        : 245
% 4.26/1.74  #Tautology    : 166
% 4.26/1.74  #SimpNegUnit  : 30
% 4.26/1.74  #BackRed      : 35
% 4.26/1.74  
% 4.26/1.74  #Partial instantiations: 0
% 4.26/1.74  #Strategies tried      : 1
% 4.26/1.74  
% 4.26/1.74  Timing (in seconds)
% 4.26/1.74  ----------------------
% 4.26/1.74  Preprocessing        : 0.36
% 4.26/1.75  Parsing              : 0.17
% 4.26/1.75  CNF conversion       : 0.03
% 4.26/1.75  Main loop            : 0.62
% 4.26/1.75  Inferencing          : 0.23
% 4.26/1.75  Reduction            : 0.20
% 4.26/1.75  Demodulation         : 0.13
% 4.26/1.75  BG Simplification    : 0.03
% 4.26/1.75  Subsumption          : 0.11
% 4.26/1.75  Abstraction          : 0.04
% 4.26/1.75  MUC search           : 0.00
% 4.26/1.75  Cooper               : 0.00
% 4.26/1.75  Total                : 1.01
% 4.26/1.75  Index Insertion      : 0.00
% 4.26/1.75  Index Deletion       : 0.00
% 4.26/1.75  Index Matching       : 0.00
% 4.26/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
