%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:37 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 124 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   78 ( 243 expanded)
%              Number of equality atoms :   11 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_94,plain,(
    ! [A_41,B_42] :
      ( k6_domain_1(A_41,B_42) = k1_tarski(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_97,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_100,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_97])).

tff(c_46,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_101,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_46])).

tff(c_106,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k6_domain_1(A_43,B_44),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_106])).

tff(c_119,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_115])).

tff(c_120,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_119])).

tff(c_8133,plain,(
    ! [B_3454,A_3455] :
      ( ~ v1_subset_1(B_3454,A_3455)
      | v1_xboole_0(B_3454)
      | ~ m1_subset_1(B_3454,k1_zfmisc_1(A_3455))
      | ~ v1_zfmisc_1(A_3455)
      | v1_xboole_0(A_3455) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8142,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_8133])).

tff(c_8154,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_101,c_8142])).

tff(c_8155,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_8154])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8160,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8155,c_2])).

tff(c_20,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8178,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8160,c_20])).

tff(c_16,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3461,plain,(
    ! [A_1677,B_1678,C_1679] :
      ( r2_hidden(A_1677,B_1678)
      | ~ r2_hidden(A_1677,C_1679)
      | r2_hidden(A_1677,k5_xboole_0(B_1678,C_1679)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3470,plain,(
    ! [A_1677,A_5] :
      ( r2_hidden(A_1677,A_5)
      | ~ r2_hidden(A_1677,k1_xboole_0)
      | r2_hidden(A_1677,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3461])).

tff(c_8193,plain,(
    ! [A_5] : r2_hidden('#skF_4',A_5) ),
    inference(resolution,[status(thm)],[c_8178,c_3470])).

tff(c_8196,plain,(
    ! [A_3456] : r2_hidden('#skF_4',A_3456) ),
    inference(resolution,[status(thm)],[c_8178,c_3470])).

tff(c_3415,plain,(
    ! [A_1666,C_1667,B_1668] :
      ( ~ r2_hidden(A_1666,C_1667)
      | ~ r2_hidden(A_1666,B_1668)
      | ~ r2_hidden(A_1666,k5_xboole_0(B_1668,C_1667)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3425,plain,(
    ! [A_1666,A_5] :
      ( ~ r2_hidden(A_1666,k1_xboole_0)
      | ~ r2_hidden(A_1666,A_5)
      | ~ r2_hidden(A_1666,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3415])).

tff(c_8206,plain,(
    ! [A_5] : ~ r2_hidden('#skF_4',A_5) ),
    inference(resolution,[status(thm)],[c_8196,c_3425])).

tff(c_8222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8193,c_8206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.92  
% 5.03/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.92  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.03/1.92  
% 5.03/1.92  %Foreground sorts:
% 5.03/1.92  
% 5.03/1.92  
% 5.03/1.92  %Background operators:
% 5.03/1.92  
% 5.03/1.92  
% 5.03/1.92  %Foreground operators:
% 5.03/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.03/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.03/1.92  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.03/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.03/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.03/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.03/1.92  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.03/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.03/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.03/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.03/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.03/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.03/1.92  tff('#skF_4', type, '#skF_4': $i).
% 5.03/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.03/1.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.03/1.92  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.03/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.03/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.03/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.03/1.92  
% 5.03/1.93  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 5.03/1.93  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.03/1.93  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.03/1.93  tff(f_91, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 5.03/1.93  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.03/1.93  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.03/1.93  tff(f_38, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.03/1.93  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.03/1.93  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.03/1.93  tff(c_44, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.03/1.93  tff(c_48, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.03/1.93  tff(c_94, plain, (![A_41, B_42]: (k6_domain_1(A_41, B_42)=k1_tarski(B_42) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.03/1.93  tff(c_97, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_94])).
% 5.03/1.93  tff(c_100, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_97])).
% 5.03/1.93  tff(c_46, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.03/1.93  tff(c_101, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_46])).
% 5.03/1.93  tff(c_106, plain, (![A_43, B_44]: (m1_subset_1(k6_domain_1(A_43, B_44), k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.03/1.93  tff(c_115, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_106])).
% 5.03/1.93  tff(c_119, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_115])).
% 5.03/1.93  tff(c_120, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_119])).
% 5.03/1.93  tff(c_8133, plain, (![B_3454, A_3455]: (~v1_subset_1(B_3454, A_3455) | v1_xboole_0(B_3454) | ~m1_subset_1(B_3454, k1_zfmisc_1(A_3455)) | ~v1_zfmisc_1(A_3455) | v1_xboole_0(A_3455))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.03/1.93  tff(c_8142, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_120, c_8133])).
% 5.03/1.93  tff(c_8154, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_101, c_8142])).
% 5.03/1.93  tff(c_8155, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_8154])).
% 5.03/1.93  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.03/1.93  tff(c_8160, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8155, c_2])).
% 5.03/1.93  tff(c_20, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.03/1.93  tff(c_8178, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8160, c_20])).
% 5.03/1.93  tff(c_16, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.03/1.93  tff(c_3461, plain, (![A_1677, B_1678, C_1679]: (r2_hidden(A_1677, B_1678) | ~r2_hidden(A_1677, C_1679) | r2_hidden(A_1677, k5_xboole_0(B_1678, C_1679)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.03/1.93  tff(c_3470, plain, (![A_1677, A_5]: (r2_hidden(A_1677, A_5) | ~r2_hidden(A_1677, k1_xboole_0) | r2_hidden(A_1677, A_5))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3461])).
% 5.03/1.93  tff(c_8193, plain, (![A_5]: (r2_hidden('#skF_4', A_5))), inference(resolution, [status(thm)], [c_8178, c_3470])).
% 5.03/1.93  tff(c_8196, plain, (![A_3456]: (r2_hidden('#skF_4', A_3456))), inference(resolution, [status(thm)], [c_8178, c_3470])).
% 5.03/1.93  tff(c_3415, plain, (![A_1666, C_1667, B_1668]: (~r2_hidden(A_1666, C_1667) | ~r2_hidden(A_1666, B_1668) | ~r2_hidden(A_1666, k5_xboole_0(B_1668, C_1667)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.03/1.93  tff(c_3425, plain, (![A_1666, A_5]: (~r2_hidden(A_1666, k1_xboole_0) | ~r2_hidden(A_1666, A_5) | ~r2_hidden(A_1666, A_5))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3415])).
% 5.03/1.93  tff(c_8206, plain, (![A_5]: (~r2_hidden('#skF_4', A_5))), inference(resolution, [status(thm)], [c_8196, c_3425])).
% 5.03/1.93  tff(c_8222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8193, c_8206])).
% 5.03/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.93  
% 5.03/1.93  Inference rules
% 5.03/1.93  ----------------------
% 5.03/1.93  #Ref     : 0
% 5.03/1.93  #Sup     : 1240
% 5.03/1.93  #Fact    : 6
% 5.03/1.93  #Define  : 0
% 5.03/1.93  #Split   : 6
% 5.03/1.93  #Chain   : 0
% 5.03/1.93  #Close   : 0
% 5.03/1.93  
% 5.03/1.93  Ordering : KBO
% 5.03/1.93  
% 5.03/1.93  Simplification rules
% 5.03/1.93  ----------------------
% 5.03/1.93  #Subsume      : 317
% 5.03/1.93  #Demod        : 293
% 5.03/1.93  #Tautology    : 152
% 5.03/1.93  #SimpNegUnit  : 15
% 5.03/1.93  #BackRed      : 19
% 5.03/1.93  
% 5.03/1.93  #Partial instantiations: 2420
% 5.03/1.93  #Strategies tried      : 1
% 5.03/1.93  
% 5.03/1.93  Timing (in seconds)
% 5.03/1.93  ----------------------
% 5.03/1.93  Preprocessing        : 0.33
% 5.03/1.93  Parsing              : 0.17
% 5.03/1.93  CNF conversion       : 0.02
% 5.03/1.93  Main loop            : 0.84
% 5.03/1.93  Inferencing          : 0.34
% 5.03/1.93  Reduction            : 0.24
% 5.03/1.94  Demodulation         : 0.16
% 5.03/1.94  BG Simplification    : 0.04
% 5.03/1.94  Subsumption          : 0.16
% 5.03/1.94  Abstraction          : 0.05
% 5.03/1.94  MUC search           : 0.00
% 5.03/1.94  Cooper               : 0.00
% 5.03/1.94  Total                : 1.20
% 5.03/1.94  Index Insertion      : 0.00
% 5.03/1.94  Index Deletion       : 0.00
% 5.03/1.94  Index Matching       : 0.00
% 5.03/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
