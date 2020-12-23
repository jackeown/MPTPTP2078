%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 103 expanded)
%              Number of leaves         :   42 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 188 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_40,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_292,plain,(
    ! [C_116,B_117,A_118] :
      ( v5_relat_1(C_116,B_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_296,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_86,c_292])).

tff(c_84,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_214,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_218,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_214])).

tff(c_90,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_88,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_402,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_406,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_402])).

tff(c_842,plain,(
    ! [B_212,A_213,C_214] :
      ( k1_xboole_0 = B_212
      | k1_relset_1(A_213,B_212,C_214) = A_213
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_845,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_86,c_842])).

tff(c_848,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_406,c_845])).

tff(c_849,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_58,plain,(
    ! [C_29,B_28,A_27] :
      ( m1_subset_1(k1_funct_1(C_29,B_28),A_27)
      | ~ r2_hidden(B_28,k1_relat_1(C_29))
      | ~ v1_funct_1(C_29)
      | ~ v5_relat_1(C_29,A_27)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_853,plain,(
    ! [B_28,A_27] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_28),A_27)
      | ~ r2_hidden(B_28,'#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_27)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_58])).

tff(c_863,plain,(
    ! [B_215,A_216] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_215),A_216)
      | ~ r2_hidden(B_215,'#skF_6')
      | ~ v5_relat_1('#skF_9',A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_90,c_853])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,(
    ! [B_46,A_47] :
      ( ~ r2_hidden(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [C_10] : ~ v1_xboole_0(k1_tarski(C_10)) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_221,plain,(
    ! [A_91,B_92] :
      ( r2_hidden(A_91,B_92)
      | v1_xboole_0(B_92)
      | ~ m1_subset_1(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_225,plain,(
    ! [A_91,A_6] :
      ( A_91 = A_6
      | v1_xboole_0(k1_tarski(A_6))
      | ~ m1_subset_1(A_91,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_221,c_8])).

tff(c_234,plain,(
    ! [A_91,A_6] :
      ( A_91 = A_6
      | ~ m1_subset_1(A_91,k1_tarski(A_6)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_225])).

tff(c_924,plain,(
    ! [B_217,A_218] :
      ( k1_funct_1('#skF_9',B_217) = A_218
      | ~ r2_hidden(B_217,'#skF_6')
      | ~ v5_relat_1('#skF_9',k1_tarski(A_218)) ) ),
    inference(resolution,[status(thm)],[c_863,c_234])).

tff(c_948,plain,(
    ! [A_219] :
      ( k1_funct_1('#skF_9','#skF_8') = A_219
      | ~ v5_relat_1('#skF_9',k1_tarski(A_219)) ) ),
    inference(resolution,[status(thm)],[c_84,c_924])).

tff(c_951,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_296,c_948])).

tff(c_955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_951])).

tff(c_956,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_112,plain,(
    ! [B_50,A_51] :
      ( ~ r1_tarski(B_50,A_51)
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_119,plain,(
    ! [C_10] : ~ r1_tarski(k1_tarski(C_10),C_10) ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_989,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_119])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.52  
% 3.06/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2
% 3.06/1.53  
% 3.06/1.53  %Foreground sorts:
% 3.06/1.53  
% 3.06/1.53  
% 3.06/1.53  %Background operators:
% 3.06/1.53  
% 3.06/1.53  
% 3.06/1.53  %Foreground operators:
% 3.06/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.06/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.06/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.06/1.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.06/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.06/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.06/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.06/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.06/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.53  
% 3.37/1.54  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.37/1.54  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.37/1.54  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.37/1.54  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.37/1.54  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.37/1.54  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.37/1.54  tff(f_80, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.37/1.54  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.37/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.37/1.54  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.37/1.54  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.37/1.54  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.54  tff(c_82, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.37/1.54  tff(c_86, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.37/1.54  tff(c_292, plain, (![C_116, B_117, A_118]: (v5_relat_1(C_116, B_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.54  tff(c_296, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_86, c_292])).
% 3.37/1.54  tff(c_84, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.37/1.54  tff(c_214, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.37/1.54  tff(c_218, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_86, c_214])).
% 3.37/1.54  tff(c_90, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.37/1.54  tff(c_88, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.37/1.54  tff(c_402, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.37/1.54  tff(c_406, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_86, c_402])).
% 3.37/1.54  tff(c_842, plain, (![B_212, A_213, C_214]: (k1_xboole_0=B_212 | k1_relset_1(A_213, B_212, C_214)=A_213 | ~v1_funct_2(C_214, A_213, B_212) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.54  tff(c_845, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_86, c_842])).
% 3.37/1.54  tff(c_848, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_406, c_845])).
% 3.37/1.54  tff(c_849, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_848])).
% 3.37/1.54  tff(c_58, plain, (![C_29, B_28, A_27]: (m1_subset_1(k1_funct_1(C_29, B_28), A_27) | ~r2_hidden(B_28, k1_relat_1(C_29)) | ~v1_funct_1(C_29) | ~v5_relat_1(C_29, A_27) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.54  tff(c_853, plain, (![B_28, A_27]: (m1_subset_1(k1_funct_1('#skF_9', B_28), A_27) | ~r2_hidden(B_28, '#skF_6') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_27) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_849, c_58])).
% 3.37/1.54  tff(c_863, plain, (![B_215, A_216]: (m1_subset_1(k1_funct_1('#skF_9', B_215), A_216) | ~r2_hidden(B_215, '#skF_6') | ~v5_relat_1('#skF_9', A_216))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_90, c_853])).
% 3.37/1.54  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.54  tff(c_93, plain, (![B_46, A_47]: (~r2_hidden(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.54  tff(c_100, plain, (![C_10]: (~v1_xboole_0(k1_tarski(C_10)))), inference(resolution, [status(thm)], [c_10, c_93])).
% 3.37/1.54  tff(c_221, plain, (![A_91, B_92]: (r2_hidden(A_91, B_92) | v1_xboole_0(B_92) | ~m1_subset_1(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.54  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.54  tff(c_225, plain, (![A_91, A_6]: (A_91=A_6 | v1_xboole_0(k1_tarski(A_6)) | ~m1_subset_1(A_91, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_221, c_8])).
% 3.37/1.54  tff(c_234, plain, (![A_91, A_6]: (A_91=A_6 | ~m1_subset_1(A_91, k1_tarski(A_6)))), inference(negUnitSimplification, [status(thm)], [c_100, c_225])).
% 3.37/1.54  tff(c_924, plain, (![B_217, A_218]: (k1_funct_1('#skF_9', B_217)=A_218 | ~r2_hidden(B_217, '#skF_6') | ~v5_relat_1('#skF_9', k1_tarski(A_218)))), inference(resolution, [status(thm)], [c_863, c_234])).
% 3.37/1.54  tff(c_948, plain, (![A_219]: (k1_funct_1('#skF_9', '#skF_8')=A_219 | ~v5_relat_1('#skF_9', k1_tarski(A_219)))), inference(resolution, [status(thm)], [c_84, c_924])).
% 3.37/1.54  tff(c_951, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_296, c_948])).
% 3.37/1.54  tff(c_955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_951])).
% 3.37/1.54  tff(c_956, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_848])).
% 3.37/1.54  tff(c_112, plain, (![B_50, A_51]: (~r1_tarski(B_50, A_51) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.54  tff(c_119, plain, (![C_10]: (~r1_tarski(k1_tarski(C_10), C_10))), inference(resolution, [status(thm)], [c_10, c_112])).
% 3.37/1.54  tff(c_989, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_956, c_119])).
% 3.37/1.54  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_989])).
% 3.37/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.54  
% 3.37/1.54  Inference rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Ref     : 0
% 3.37/1.54  #Sup     : 194
% 3.37/1.54  #Fact    : 2
% 3.37/1.54  #Define  : 0
% 3.37/1.54  #Split   : 1
% 3.37/1.54  #Chain   : 0
% 3.37/1.54  #Close   : 0
% 3.37/1.54  
% 3.37/1.54  Ordering : KBO
% 3.37/1.54  
% 3.37/1.54  Simplification rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Subsume      : 36
% 3.37/1.54  #Demod        : 74
% 3.37/1.54  #Tautology    : 72
% 3.37/1.54  #SimpNegUnit  : 19
% 3.37/1.54  #BackRed      : 5
% 3.37/1.54  
% 3.37/1.54  #Partial instantiations: 0
% 3.37/1.54  #Strategies tried      : 1
% 3.37/1.54  
% 3.37/1.54  Timing (in seconds)
% 3.37/1.54  ----------------------
% 3.37/1.54  Preprocessing        : 0.35
% 3.37/1.54  Parsing              : 0.17
% 3.37/1.54  CNF conversion       : 0.03
% 3.37/1.54  Main loop            : 0.40
% 3.37/1.54  Inferencing          : 0.14
% 3.37/1.54  Reduction            : 0.12
% 3.37/1.54  Demodulation         : 0.08
% 3.37/1.54  BG Simplification    : 0.03
% 3.37/1.54  Subsumption          : 0.08
% 3.37/1.54  Abstraction          : 0.03
% 3.37/1.54  MUC search           : 0.00
% 3.37/1.54  Cooper               : 0.00
% 3.37/1.54  Total                : 0.78
% 3.37/1.54  Index Insertion      : 0.00
% 3.37/1.54  Index Deletion       : 0.00
% 3.37/1.54  Index Matching       : 0.00
% 3.37/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
