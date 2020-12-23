%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:09 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   68 (  92 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 170 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_80,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_209,plain,(
    ! [C_97,B_98,A_99] :
      ( v5_relat_1(C_97,B_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_213,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_209])).

tff(c_78,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_143,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_143])).

tff(c_84,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_82,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_269,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_273,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_269])).

tff(c_582,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_585,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_582])).

tff(c_588,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_273,c_585])).

tff(c_589,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_495,plain,(
    ! [B_159,C_160,A_161] :
      ( r2_hidden(k1_funct_1(B_159,C_160),A_161)
      | ~ r2_hidden(C_160,k1_relat_1(B_159))
      | ~ v1_funct_1(B_159)
      | ~ v5_relat_1(B_159,A_161)
      | ~ v1_relat_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_524,plain,(
    ! [B_159,C_160,A_2] :
      ( k1_funct_1(B_159,C_160) = A_2
      | ~ r2_hidden(C_160,k1_relat_1(B_159))
      | ~ v1_funct_1(B_159)
      | ~ v5_relat_1(B_159,k1_tarski(A_2))
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_495,c_4])).

tff(c_596,plain,(
    ! [C_160,A_2] :
      ( k1_funct_1('#skF_8',C_160) = A_2
      | ~ r2_hidden(C_160,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_524])).

tff(c_614,plain,(
    ! [C_180,A_181] :
      ( k1_funct_1('#skF_8',C_180) = A_181
      | ~ r2_hidden(C_180,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_181)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_84,c_596])).

tff(c_631,plain,(
    ! [A_187] :
      ( k1_funct_1('#skF_8','#skF_7') = A_187
      | ~ v5_relat_1('#skF_8',k1_tarski(A_187)) ) ),
    inference(resolution,[status(thm)],[c_78,c_614])).

tff(c_634,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_213,c_631])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_634])).

tff(c_639,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [B_44,A_45] :
      ( ~ r1_tarski(B_44,A_45)
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_109,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_657,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_109])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:07:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_1
% 3.36/1.50  
% 3.36/1.50  %Foreground sorts:
% 3.36/1.50  
% 3.36/1.50  
% 3.36/1.50  %Background operators:
% 3.36/1.50  
% 3.36/1.50  
% 3.36/1.50  %Foreground operators:
% 3.36/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.36/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.36/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.36/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.36/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.36/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.36/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.36/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.36/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.50  
% 3.36/1.52  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.52  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.36/1.52  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.36/1.52  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.36/1.52  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.36/1.52  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.36/1.52  tff(f_69, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.36/1.52  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.36/1.52  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.36/1.52  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.52  tff(c_76, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.36/1.52  tff(c_80, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.36/1.52  tff(c_209, plain, (![C_97, B_98, A_99]: (v5_relat_1(C_97, B_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.36/1.52  tff(c_213, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_80, c_209])).
% 3.36/1.52  tff(c_78, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.36/1.52  tff(c_143, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.52  tff(c_147, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_80, c_143])).
% 3.36/1.52  tff(c_84, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.36/1.52  tff(c_82, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.36/1.52  tff(c_269, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.36/1.52  tff(c_273, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_80, c_269])).
% 3.36/1.52  tff(c_582, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.36/1.52  tff(c_585, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_80, c_582])).
% 3.36/1.52  tff(c_588, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_273, c_585])).
% 3.36/1.52  tff(c_589, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_588])).
% 3.36/1.52  tff(c_495, plain, (![B_159, C_160, A_161]: (r2_hidden(k1_funct_1(B_159, C_160), A_161) | ~r2_hidden(C_160, k1_relat_1(B_159)) | ~v1_funct_1(B_159) | ~v5_relat_1(B_159, A_161) | ~v1_relat_1(B_159))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.36/1.52  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.52  tff(c_524, plain, (![B_159, C_160, A_2]: (k1_funct_1(B_159, C_160)=A_2 | ~r2_hidden(C_160, k1_relat_1(B_159)) | ~v1_funct_1(B_159) | ~v5_relat_1(B_159, k1_tarski(A_2)) | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_495, c_4])).
% 3.36/1.52  tff(c_596, plain, (![C_160, A_2]: (k1_funct_1('#skF_8', C_160)=A_2 | ~r2_hidden(C_160, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_tarski(A_2)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_524])).
% 3.36/1.52  tff(c_614, plain, (![C_180, A_181]: (k1_funct_1('#skF_8', C_180)=A_181 | ~r2_hidden(C_180, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_181)))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_84, c_596])).
% 3.36/1.52  tff(c_631, plain, (![A_187]: (k1_funct_1('#skF_8', '#skF_7')=A_187 | ~v5_relat_1('#skF_8', k1_tarski(A_187)))), inference(resolution, [status(thm)], [c_78, c_614])).
% 3.36/1.52  tff(c_634, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_213, c_631])).
% 3.36/1.52  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_634])).
% 3.36/1.52  tff(c_639, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_588])).
% 3.36/1.52  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.52  tff(c_102, plain, (![B_44, A_45]: (~r1_tarski(B_44, A_45) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.52  tff(c_109, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.36/1.52  tff(c_657, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_639, c_109])).
% 3.36/1.52  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_657])).
% 3.36/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.52  
% 3.36/1.52  Inference rules
% 3.36/1.52  ----------------------
% 3.36/1.52  #Ref     : 0
% 3.36/1.52  #Sup     : 127
% 3.36/1.52  #Fact    : 0
% 3.36/1.52  #Define  : 0
% 3.36/1.52  #Split   : 2
% 3.36/1.52  #Chain   : 0
% 3.36/1.52  #Close   : 0
% 3.36/1.52  
% 3.36/1.52  Ordering : KBO
% 3.36/1.52  
% 3.36/1.52  Simplification rules
% 3.36/1.52  ----------------------
% 3.36/1.52  #Subsume      : 20
% 3.36/1.52  #Demod        : 47
% 3.36/1.52  #Tautology    : 49
% 3.36/1.52  #SimpNegUnit  : 1
% 3.36/1.52  #BackRed      : 5
% 3.36/1.52  
% 3.36/1.52  #Partial instantiations: 0
% 3.36/1.52  #Strategies tried      : 1
% 3.36/1.52  
% 3.36/1.52  Timing (in seconds)
% 3.36/1.52  ----------------------
% 3.36/1.52  Preprocessing        : 0.35
% 3.36/1.52  Parsing              : 0.17
% 3.36/1.52  CNF conversion       : 0.03
% 3.36/1.52  Main loop            : 0.41
% 3.36/1.52  Inferencing          : 0.14
% 3.36/1.52  Reduction            : 0.12
% 3.36/1.52  Demodulation         : 0.08
% 3.36/1.52  BG Simplification    : 0.03
% 3.36/1.52  Subsumption          : 0.08
% 3.36/1.52  Abstraction          : 0.03
% 3.36/1.52  MUC search           : 0.00
% 3.36/1.52  Cooper               : 0.00
% 3.36/1.52  Total                : 0.80
% 3.36/1.52  Index Insertion      : 0.00
% 3.36/1.52  Index Deletion       : 0.00
% 3.36/1.52  Index Matching       : 0.00
% 3.36/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
