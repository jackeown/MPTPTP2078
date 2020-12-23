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
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 104 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 353 expanded)
%              Number of equality atoms :   25 (  99 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_14,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ! [D_29,C_30,B_31,A_32] :
      ( k1_funct_1(k2_funct_1(D_29),k1_funct_1(D_29,C_30)) = C_30
      | k1_xboole_0 = B_31
      | ~ r2_hidden(C_30,A_32)
      | ~ v2_funct_1(D_29)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_32,B_31)))
      | ~ v1_funct_2(D_29,A_32,B_31)
      | ~ v1_funct_1(D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_86,plain,(
    ! [D_38,B_39] :
      ( k1_funct_1(k2_funct_1(D_38),k1_funct_1(D_38,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_39
      | ~ v2_funct_1(D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_39)))
      | ~ v1_funct_2(D_38,'#skF_1',B_39)
      | ~ v1_funct_1(D_38) ) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_91,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_98,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_16,c_91])).

tff(c_100,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_119,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_56])).

tff(c_34,plain,(
    ! [B_16,A_17] :
      ( ~ r1_tarski(B_16,A_17)
      | ~ r2_hidden(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_34])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_42])).

tff(c_135,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_136,plain,(
    ! [D_42,B_43] :
      ( k1_funct_1(k2_funct_1(D_42),k1_funct_1(D_42,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_43
      | ~ v2_funct_1(D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_43)))
      | ~ v1_funct_2(D_42,'#skF_1',B_43)
      | ~ v1_funct_1(D_42) ) ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_141,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_148,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_141])).

tff(c_149,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_148])).

tff(c_134,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_155,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_134])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.27  
% 2.02/1.27  %Foreground sorts:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Background operators:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Foreground operators:
% 2.02/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.02/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.02/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.27  
% 2.02/1.29  tff(f_74, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.02/1.29  tff(f_56, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.02/1.29  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.02/1.29  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.02/1.29  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.02/1.29  tff(c_14, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_16, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_70, plain, (![D_29, C_30, B_31, A_32]: (k1_funct_1(k2_funct_1(D_29), k1_funct_1(D_29, C_30))=C_30 | k1_xboole_0=B_31 | ~r2_hidden(C_30, A_32) | ~v2_funct_1(D_29) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_32, B_31))) | ~v1_funct_2(D_29, A_32, B_31) | ~v1_funct_1(D_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.29  tff(c_86, plain, (![D_38, B_39]: (k1_funct_1(k2_funct_1(D_38), k1_funct_1(D_38, '#skF_3'))='#skF_3' | k1_xboole_0=B_39 | ~v2_funct_1(D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_39))) | ~v1_funct_2(D_38, '#skF_1', B_39) | ~v1_funct_1(D_38))), inference(resolution, [status(thm)], [c_20, c_70])).
% 2.02/1.29  tff(c_91, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_86])).
% 2.02/1.29  tff(c_98, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_16, c_91])).
% 2.02/1.29  tff(c_100, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_98])).
% 2.02/1.29  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.29  tff(c_44, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.29  tff(c_56, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.02/1.29  tff(c_119, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_56])).
% 2.02/1.29  tff(c_34, plain, (![B_16, A_17]: (~r1_tarski(B_16, A_17) | ~r2_hidden(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.29  tff(c_42, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_34])).
% 2.02/1.29  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_42])).
% 2.02/1.29  tff(c_135, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_98])).
% 2.02/1.29  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.29  tff(c_136, plain, (![D_42, B_43]: (k1_funct_1(k2_funct_1(D_42), k1_funct_1(D_42, '#skF_4'))='#skF_4' | k1_xboole_0=B_43 | ~v2_funct_1(D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_43))) | ~v1_funct_2(D_42, '#skF_1', B_43) | ~v1_funct_1(D_42))), inference(resolution, [status(thm)], [c_18, c_70])).
% 2.02/1.29  tff(c_141, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_136])).
% 2.02/1.29  tff(c_148, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_141])).
% 2.02/1.29  tff(c_149, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_135, c_148])).
% 2.02/1.29  tff(c_134, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_98])).
% 2.02/1.29  tff(c_155, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_134])).
% 2.02/1.29  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_155])).
% 2.02/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  Inference rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Ref     : 0
% 2.02/1.29  #Sup     : 27
% 2.02/1.29  #Fact    : 0
% 2.02/1.29  #Define  : 0
% 2.02/1.29  #Split   : 1
% 2.02/1.29  #Chain   : 0
% 2.02/1.29  #Close   : 0
% 2.02/1.29  
% 2.02/1.29  Ordering : KBO
% 2.02/1.29  
% 2.02/1.29  Simplification rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Subsume      : 0
% 2.02/1.29  #Demod        : 21
% 2.02/1.29  #Tautology    : 7
% 2.02/1.29  #SimpNegUnit  : 2
% 2.02/1.29  #BackRed      : 11
% 2.02/1.29  
% 2.02/1.29  #Partial instantiations: 0
% 2.02/1.29  #Strategies tried      : 1
% 2.02/1.29  
% 2.02/1.29  Timing (in seconds)
% 2.02/1.29  ----------------------
% 2.02/1.29  Preprocessing        : 0.32
% 2.02/1.29  Parsing              : 0.18
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.19
% 2.02/1.29  Inferencing          : 0.07
% 2.02/1.29  Reduction            : 0.06
% 2.02/1.29  Demodulation         : 0.04
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.03
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.29  MUC search           : 0.00
% 2.02/1.29  Cooper               : 0.00
% 2.02/1.29  Total                : 0.54
% 2.02/1.29  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
