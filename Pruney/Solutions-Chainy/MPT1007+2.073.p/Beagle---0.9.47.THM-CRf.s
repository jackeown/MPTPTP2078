%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:21 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 ( 110 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_66,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_69])).

tff(c_78,plain,(
    ! [C_36,B_37,A_38] :
      ( v5_relat_1(C_36,B_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_133,plain,(
    ! [B_59,C_60,A_61] :
      ( r2_hidden(k1_funct_1(B_59,C_60),A_61)
      | ~ r2_hidden(C_60,k1_relat_1(B_59))
      | ~ v1_funct_1(B_59)
      | ~ v5_relat_1(B_59,A_61)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_140,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_40])).

tff(c_144,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_82,c_48,c_140])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_166,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 = B_70
      | k1_relset_1(A_71,B_70,C_72) = A_71
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_166])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_88,c_169])).

tff(c_173,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_172])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_193,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_4])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.41  
% 2.34/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.34/1.41  
% 2.34/1.41  %Foreground sorts:
% 2.34/1.41  
% 2.34/1.41  
% 2.34/1.41  %Background operators:
% 2.34/1.41  
% 2.34/1.41  
% 2.34/1.41  %Foreground operators:
% 2.34/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.34/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.34/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.34/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.41  
% 2.34/1.42  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.34/1.42  tff(f_94, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.34/1.42  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.34/1.42  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.34/1.42  tff(f_54, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.34/1.42  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.34/1.42  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.34/1.42  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.34/1.42  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.42  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.42  tff(c_66, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.42  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_66])).
% 2.34/1.42  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_69])).
% 2.34/1.42  tff(c_78, plain, (![C_36, B_37, A_38]: (v5_relat_1(C_36, B_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_37))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.34/1.42  tff(c_82, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_78])).
% 2.34/1.42  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.42  tff(c_133, plain, (![B_59, C_60, A_61]: (r2_hidden(k1_funct_1(B_59, C_60), A_61) | ~r2_hidden(C_60, k1_relat_1(B_59)) | ~v1_funct_1(B_59) | ~v5_relat_1(B_59, A_61) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.34/1.42  tff(c_40, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.42  tff(c_140, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_133, c_40])).
% 2.34/1.42  tff(c_144, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_82, c_48, c_140])).
% 2.34/1.42  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.42  tff(c_46, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.42  tff(c_84, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.34/1.42  tff(c_88, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_84])).
% 2.34/1.42  tff(c_166, plain, (![B_70, A_71, C_72]: (k1_xboole_0=B_70 | k1_relset_1(A_71, B_70, C_72)=A_71 | ~v1_funct_2(C_72, A_71, B_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.34/1.42  tff(c_169, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_44, c_166])).
% 2.34/1.42  tff(c_172, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_88, c_169])).
% 2.34/1.42  tff(c_173, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_172])).
% 2.34/1.42  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.42  tff(c_193, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_4])).
% 2.34/1.42  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_193])).
% 2.34/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.42  
% 2.34/1.42  Inference rules
% 2.34/1.42  ----------------------
% 2.34/1.42  #Ref     : 0
% 2.34/1.42  #Sup     : 30
% 2.34/1.42  #Fact    : 0
% 2.34/1.42  #Define  : 0
% 2.34/1.42  #Split   : 0
% 2.34/1.42  #Chain   : 0
% 2.34/1.43  #Close   : 0
% 2.34/1.43  
% 2.34/1.43  Ordering : KBO
% 2.34/1.43  
% 2.34/1.43  Simplification rules
% 2.34/1.43  ----------------------
% 2.34/1.43  #Subsume      : 0
% 2.34/1.43  #Demod        : 22
% 2.34/1.43  #Tautology    : 12
% 2.34/1.43  #SimpNegUnit  : 3
% 2.34/1.43  #BackRed      : 4
% 2.34/1.43  
% 2.34/1.43  #Partial instantiations: 0
% 2.34/1.43  #Strategies tried      : 1
% 2.34/1.43  
% 2.34/1.43  Timing (in seconds)
% 2.34/1.43  ----------------------
% 2.34/1.43  Preprocessing        : 0.36
% 2.34/1.43  Parsing              : 0.19
% 2.34/1.43  CNF conversion       : 0.03
% 2.34/1.43  Main loop            : 0.19
% 2.34/1.43  Inferencing          : 0.07
% 2.34/1.43  Reduction            : 0.06
% 2.34/1.43  Demodulation         : 0.04
% 2.34/1.43  BG Simplification    : 0.02
% 2.34/1.43  Subsumption          : 0.04
% 2.34/1.43  Abstraction          : 0.01
% 2.34/1.43  MUC search           : 0.00
% 2.34/1.43  Cooper               : 0.00
% 2.34/1.43  Total                : 0.57
% 2.34/1.43  Index Insertion      : 0.00
% 2.34/1.43  Index Deletion       : 0.00
% 2.34/1.43  Index Matching       : 0.00
% 2.34/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
