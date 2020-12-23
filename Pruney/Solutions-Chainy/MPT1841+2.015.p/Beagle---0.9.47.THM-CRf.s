%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:30 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 115 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_118,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_118])).

tff(c_124,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_121])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_125,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_40])).

tff(c_130,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_139,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_130])).

tff(c_143,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_139])).

tff(c_144,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_143])).

tff(c_154,plain,(
    ! [B_53,A_54] :
      ( ~ v1_subset_1(B_53,A_54)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_157,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_154])).

tff(c_163,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_125,c_157])).

tff(c_164,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_49,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [D_8,A_3] : r2_hidden(D_8,k2_tarski(A_3,D_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_8])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_34] : ~ r1_tarski(k1_tarski(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_73,c_30])).

tff(c_184,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_77])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.22  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.92/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.92/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.92/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.22  
% 2.02/1.23  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.02/1.23  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.02/1.23  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.02/1.23  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.02/1.23  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.02/1.23  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.23  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.02/1.23  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.02/1.23  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.02/1.23  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.23  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.02/1.23  tff(c_38, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.02/1.23  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.02/1.23  tff(c_118, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.02/1.23  tff(c_121, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_118])).
% 2.02/1.23  tff(c_124, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_121])).
% 2.02/1.23  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.02/1.23  tff(c_125, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_40])).
% 2.02/1.23  tff(c_130, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.23  tff(c_139, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_130])).
% 2.02/1.23  tff(c_143, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_139])).
% 2.02/1.23  tff(c_144, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_143])).
% 2.02/1.23  tff(c_154, plain, (![B_53, A_54]: (~v1_subset_1(B_53, A_54) | v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.23  tff(c_157, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_144, c_154])).
% 2.02/1.23  tff(c_163, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_125, c_157])).
% 2.02/1.23  tff(c_164, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 2.02/1.23  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.23  tff(c_169, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_2])).
% 2.02/1.23  tff(c_49, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.23  tff(c_8, plain, (![D_8, A_3]: (r2_hidden(D_8, k2_tarski(A_3, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.23  tff(c_73, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_8])).
% 2.02/1.23  tff(c_30, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.23  tff(c_77, plain, (![A_34]: (~r1_tarski(k1_tarski(A_34), A_34))), inference(resolution, [status(thm)], [c_73, c_30])).
% 2.02/1.23  tff(c_184, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_169, c_77])).
% 2.02/1.23  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_184])).
% 2.02/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 32
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 1
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 3
% 2.02/1.23  #Demod        : 10
% 2.02/1.23  #Tautology    : 12
% 2.02/1.23  #SimpNegUnit  : 3
% 2.02/1.23  #BackRed      : 5
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.02/1.23  Preprocessing        : 0.29
% 2.02/1.23  Parsing              : 0.15
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.15
% 2.02/1.23  Inferencing          : 0.05
% 2.02/1.24  Reduction            : 0.05
% 2.02/1.24  Demodulation         : 0.03
% 2.02/1.24  BG Simplification    : 0.01
% 2.02/1.24  Subsumption          : 0.03
% 2.02/1.24  Abstraction          : 0.01
% 2.02/1.24  MUC search           : 0.00
% 2.02/1.24  Cooper               : 0.00
% 2.02/1.24  Total                : 0.47
% 2.02/1.24  Index Insertion      : 0.00
% 2.02/1.24  Index Deletion       : 0.00
% 2.02/1.24  Index Matching       : 0.00
% 2.02/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
