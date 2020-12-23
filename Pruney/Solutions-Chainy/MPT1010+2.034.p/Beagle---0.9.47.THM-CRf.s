%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:09 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   64 (  87 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 163 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_46,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_100,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_100])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_81,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_108,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_112,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_181,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_184,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_181])).

tff(c_187,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_112,c_184])).

tff(c_188,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_155,plain,(
    ! [B_68,C_69,A_70] :
      ( r2_hidden(k1_funct_1(B_68,C_69),A_70)
      | ~ r2_hidden(C_69,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v5_relat_1(B_68,A_70)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    ! [B_68,C_69,A_1] :
      ( k1_funct_1(B_68,C_69) = A_1
      | ~ r2_hidden(C_69,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v5_relat_1(B_68,k1_tarski(A_1))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_155,c_4])).

tff(c_192,plain,(
    ! [C_69,A_1] :
      ( k1_funct_1('#skF_6',C_69) = A_1
      | ~ r2_hidden(C_69,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_1))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_160])).

tff(c_202,plain,(
    ! [C_82,A_83] :
      ( k1_funct_1('#skF_6',C_82) = A_83
      | ~ r2_hidden(C_82,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_83)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54,c_192])).

tff(c_218,plain,(
    ! [A_84] :
      ( k1_funct_1('#skF_6','#skF_5') = A_84
      | ~ v5_relat_1('#skF_6',k1_tarski(A_84)) ) ),
    inference(resolution,[status(thm)],[c_48,c_202])).

tff(c_221,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_104,c_218])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_221])).

tff(c_226,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_22,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_249,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_22])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.23/1.25  
% 2.23/1.25  %Foreground sorts:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Background operators:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Foreground operators:
% 2.23/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.25  
% 2.23/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.26  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.23/1.26  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.23/1.26  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.23/1.26  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.23/1.26  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.23/1.27  tff(f_53, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.23/1.27  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.23/1.27  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.23/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.27  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.23/1.27  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.23/1.27  tff(c_100, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.23/1.27  tff(c_104, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_100])).
% 2.23/1.27  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.23/1.27  tff(c_81, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.27  tff(c_85, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_81])).
% 2.23/1.27  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.23/1.27  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.23/1.27  tff(c_108, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.27  tff(c_112, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_108])).
% 2.23/1.27  tff(c_181, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.27  tff(c_184, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_181])).
% 2.23/1.27  tff(c_187, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_112, c_184])).
% 2.23/1.27  tff(c_188, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_187])).
% 2.23/1.27  tff(c_155, plain, (![B_68, C_69, A_70]: (r2_hidden(k1_funct_1(B_68, C_69), A_70) | ~r2_hidden(C_69, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v5_relat_1(B_68, A_70) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.27  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.27  tff(c_160, plain, (![B_68, C_69, A_1]: (k1_funct_1(B_68, C_69)=A_1 | ~r2_hidden(C_69, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v5_relat_1(B_68, k1_tarski(A_1)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_155, c_4])).
% 2.23/1.27  tff(c_192, plain, (![C_69, A_1]: (k1_funct_1('#skF_6', C_69)=A_1 | ~r2_hidden(C_69, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_tarski(A_1)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_160])).
% 2.23/1.27  tff(c_202, plain, (![C_82, A_83]: (k1_funct_1('#skF_6', C_82)=A_83 | ~r2_hidden(C_82, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54, c_192])).
% 2.23/1.27  tff(c_218, plain, (![A_84]: (k1_funct_1('#skF_6', '#skF_5')=A_84 | ~v5_relat_1('#skF_6', k1_tarski(A_84)))), inference(resolution, [status(thm)], [c_48, c_202])).
% 2.23/1.27  tff(c_221, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_104, c_218])).
% 2.23/1.27  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_221])).
% 2.23/1.27  tff(c_226, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 2.23/1.27  tff(c_22, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.27  tff(c_249, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_226, c_22])).
% 2.23/1.27  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_249])).
% 2.23/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  Inference rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Ref     : 0
% 2.23/1.27  #Sup     : 44
% 2.23/1.27  #Fact    : 0
% 2.23/1.27  #Define  : 0
% 2.23/1.27  #Split   : 1
% 2.23/1.27  #Chain   : 0
% 2.23/1.27  #Close   : 0
% 2.23/1.27  
% 2.23/1.27  Ordering : KBO
% 2.23/1.27  
% 2.23/1.27  Simplification rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Subsume      : 0
% 2.23/1.27  #Demod        : 22
% 2.23/1.27  #Tautology    : 20
% 2.23/1.27  #SimpNegUnit  : 1
% 2.23/1.27  #BackRed      : 5
% 2.23/1.27  
% 2.23/1.27  #Partial instantiations: 0
% 2.23/1.27  #Strategies tried      : 1
% 2.23/1.27  
% 2.23/1.27  Timing (in seconds)
% 2.23/1.27  ----------------------
% 2.23/1.27  Preprocessing        : 0.31
% 2.23/1.27  Parsing              : 0.15
% 2.23/1.27  CNF conversion       : 0.02
% 2.23/1.27  Main loop            : 0.21
% 2.23/1.27  Inferencing          : 0.07
% 2.23/1.27  Reduction            : 0.06
% 2.23/1.27  Demodulation         : 0.04
% 2.23/1.27  BG Simplification    : 0.02
% 2.23/1.27  Subsumption          : 0.04
% 2.23/1.27  Abstraction          : 0.01
% 2.41/1.27  MUC search           : 0.00
% 2.41/1.27  Cooper               : 0.00
% 2.41/1.27  Total                : 0.54
% 2.41/1.27  Index Insertion      : 0.00
% 2.41/1.27  Index Deletion       : 0.00
% 2.41/1.27  Index Matching       : 0.00
% 2.41/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
