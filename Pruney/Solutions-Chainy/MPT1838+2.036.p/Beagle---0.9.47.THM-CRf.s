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
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 139 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_22] :
      ( k6_domain_1(A_22,'#skF_2'(A_22)) = A_22
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_2'(A_22),A_22)
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_195,plain,(
    ! [A_55,B_56] :
      ( k6_domain_1(A_55,B_56) = k1_tarski(B_56)
      | ~ m1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_224,plain,(
    ! [A_64] :
      ( k6_domain_1(A_64,'#skF_2'(A_64)) = k1_tarski('#skF_2'(A_64))
      | ~ v1_zfmisc_1(A_64)
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_293,plain,(
    ! [A_71] :
      ( k1_tarski('#skF_2'(A_71)) = A_71
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_224])).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(k1_tarski(A_48),B_49) = B_49
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),B_19) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_170,plain,(
    ! [B_51,A_52] :
      ( k1_xboole_0 != B_51
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_22])).

tff(c_186,plain,(
    ! [A_54] :
      ( k1_xboole_0 != A_54
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_194,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_186,c_40])).

tff(c_193,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_186,c_38])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_206,plain,(
    ! [C_60,B_61,A_62] :
      ( k1_xboole_0 = C_60
      | k1_xboole_0 = B_61
      | C_60 = B_61
      | k2_xboole_0(B_61,C_60) != k1_tarski(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_215,plain,(
    ! [A_62] :
      ( k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | '#skF_3' = '#skF_4'
      | k1_tarski(A_62) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_206])).

tff(c_221,plain,(
    ! [A_62] : k1_tarski(A_62) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_194,c_193,c_215])).

tff(c_332,plain,(
    ! [A_72] :
      ( A_72 != '#skF_4'
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72)
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_221])).

tff(c_334,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_332])).

tff(c_337,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_334])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.20/1.23  
% 2.20/1.23  %Foreground sorts:
% 2.20/1.23  
% 2.20/1.23  
% 2.20/1.23  %Background operators:
% 2.20/1.23  
% 2.20/1.23  
% 2.20/1.23  %Foreground operators:
% 2.20/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.20/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.20/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.23  
% 2.20/1.24  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.20/1.24  tff(f_79, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.20/1.24  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.20/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.24  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.20/1.24  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.20/1.24  tff(f_62, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.20/1.24  tff(f_59, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.20/1.24  tff(c_38, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.24  tff(c_36, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.24  tff(c_28, plain, (![A_22]: (k6_domain_1(A_22, '#skF_2'(A_22))=A_22 | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.24  tff(c_30, plain, (![A_22]: (m1_subset_1('#skF_2'(A_22), A_22) | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.24  tff(c_195, plain, (![A_55, B_56]: (k6_domain_1(A_55, B_56)=k1_tarski(B_56) | ~m1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.24  tff(c_224, plain, (![A_64]: (k6_domain_1(A_64, '#skF_2'(A_64))=k1_tarski('#skF_2'(A_64)) | ~v1_zfmisc_1(A_64) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_30, c_195])).
% 2.20/1.24  tff(c_293, plain, (![A_71]: (k1_tarski('#skF_2'(A_71))=A_71 | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71))), inference(superposition, [status(thm), theory('equality')], [c_28, c_224])).
% 2.20/1.24  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.24  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.24  tff(c_89, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.24  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.24  tff(c_134, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)=B_49 | ~r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_89, c_6])).
% 2.20/1.24  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.24  tff(c_170, plain, (![B_51, A_52]: (k1_xboole_0!=B_51 | ~r2_hidden(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_134, c_22])).
% 2.20/1.24  tff(c_186, plain, (![A_54]: (k1_xboole_0!=A_54 | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_4, c_170])).
% 2.20/1.24  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.24  tff(c_194, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_186, c_40])).
% 2.20/1.24  tff(c_193, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_186, c_38])).
% 2.20/1.24  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.24  tff(c_71, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.24  tff(c_75, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.20/1.24  tff(c_206, plain, (![C_60, B_61, A_62]: (k1_xboole_0=C_60 | k1_xboole_0=B_61 | C_60=B_61 | k2_xboole_0(B_61, C_60)!=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.20/1.24  tff(c_215, plain, (![A_62]: (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | '#skF_3'='#skF_4' | k1_tarski(A_62)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75, c_206])).
% 2.20/1.24  tff(c_221, plain, (![A_62]: (k1_tarski(A_62)!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_194, c_193, c_215])).
% 2.20/1.24  tff(c_332, plain, (![A_72]: (A_72!='#skF_4' | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72) | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72))), inference(superposition, [status(thm), theory('equality')], [c_293, c_221])).
% 2.20/1.24  tff(c_334, plain, (~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_332])).
% 2.20/1.24  tff(c_337, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_334])).
% 2.20/1.24  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_337])).
% 2.20/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  Inference rules
% 2.20/1.24  ----------------------
% 2.20/1.24  #Ref     : 1
% 2.20/1.24  #Sup     : 75
% 2.20/1.24  #Fact    : 0
% 2.20/1.24  #Define  : 0
% 2.20/1.24  #Split   : 0
% 2.20/1.24  #Chain   : 0
% 2.20/1.24  #Close   : 0
% 2.20/1.24  
% 2.20/1.24  Ordering : KBO
% 2.20/1.24  
% 2.20/1.24  Simplification rules
% 2.20/1.24  ----------------------
% 2.20/1.24  #Subsume      : 9
% 2.20/1.24  #Demod        : 2
% 2.20/1.24  #Tautology    : 32
% 2.20/1.24  #SimpNegUnit  : 6
% 2.20/1.24  #BackRed      : 0
% 2.20/1.24  
% 2.20/1.24  #Partial instantiations: 0
% 2.20/1.24  #Strategies tried      : 1
% 2.20/1.24  
% 2.20/1.24  Timing (in seconds)
% 2.20/1.24  ----------------------
% 2.20/1.24  Preprocessing        : 0.29
% 2.20/1.24  Parsing              : 0.16
% 2.20/1.24  CNF conversion       : 0.02
% 2.20/1.24  Main loop            : 0.20
% 2.20/1.24  Inferencing          : 0.08
% 2.20/1.24  Reduction            : 0.06
% 2.20/1.24  Demodulation         : 0.03
% 2.20/1.24  BG Simplification    : 0.02
% 2.20/1.24  Subsumption          : 0.03
% 2.20/1.24  Abstraction          : 0.01
% 2.20/1.24  MUC search           : 0.00
% 2.20/1.24  Cooper               : 0.00
% 2.20/1.24  Total                : 0.52
% 2.20/1.24  Index Insertion      : 0.00
% 2.20/1.24  Index Deletion       : 0.00
% 2.20/1.25  Index Matching       : 0.00
% 2.20/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
