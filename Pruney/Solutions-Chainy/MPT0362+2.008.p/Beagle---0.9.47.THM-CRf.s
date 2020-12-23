%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:33 EST 2020

% Result     : Theorem 10.46s
% Output     : CNFRefutation 10.46s
% Verified   : 
% Statistics : Number of formulae       :   60 (  75 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 115 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [A_44,B_45] : r1_tarski(k3_xboole_0(A_44,B_45),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_115,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [B_50,A_14] :
      ( r1_tarski(B_50,A_14)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_115,c_16])).

tff(c_127,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_122])).

tff(c_144,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_127])).

tff(c_153,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,'#skF_3')
      | ~ r1_tarski(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_153])).

tff(c_18,plain,(
    ! [C_18,A_14] :
      ( r2_hidden(C_18,k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    ! [B_40,A_41] :
      ( m1_subset_1(B_40,A_41)
      | ~ r2_hidden(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_74,plain,(
    ! [C_18,A_14] :
      ( m1_subset_1(C_18,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_77,plain,(
    ! [C_18,A_14] :
      ( m1_subset_1(C_18,k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_74])).

tff(c_176,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_894,plain,(
    ! [A_116,C_117] :
      ( k4_xboole_0(A_116,C_117) = k3_subset_1(A_116,C_117)
      | ~ r1_tarski(C_117,A_116) ) ),
    inference(resolution,[status(thm)],[c_77,c_176])).

tff(c_3333,plain,(
    ! [A_219] :
      ( k4_xboole_0('#skF_3',A_219) = k3_subset_1('#skF_3',A_219)
      | ~ r1_tarski(A_219,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_164,c_894])).

tff(c_17307,plain,(
    ! [B_527] : k4_xboole_0('#skF_3',k3_xboole_0('#skF_4',B_527)) = k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_527)) ),
    inference(resolution,[status(thm)],[c_92,c_3333])).

tff(c_193,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_1269,plain,(
    ! [A_128,D_129,B_130,C_131] :
      ( r1_tarski(k4_xboole_0(A_128,D_129),k4_xboole_0(B_130,C_131))
      | ~ r1_tarski(C_131,D_129)
      | ~ r1_tarski(A_128,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1308,plain,(
    ! [B_130,C_131] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0(B_130,C_131))
      | ~ r1_tarski(C_131,'#skF_4')
      | ~ r1_tarski('#skF_3',B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1269])).

tff(c_17437,plain,(
    ! [B_527] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_527)))
      | ~ r1_tarski(k3_xboole_0('#skF_4',B_527),'#skF_4')
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17307,c_1308])).

tff(c_17513,plain,(
    ! [B_527] : r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_527))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92,c_17437])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_314,plain,(
    ! [A_69,B_70,C_71] :
      ( k9_subset_1(A_69,B_70,C_71) = k3_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_326,plain,(
    ! [B_70] : k9_subset_1('#skF_3',B_70,'#skF_5') = k3_xboole_0(B_70,'#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_314])).

tff(c_42,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_328,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_42])).

tff(c_17974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17513,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.46/4.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.46/4.26  
% 10.46/4.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.46/4.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.46/4.26  
% 10.46/4.26  %Foreground sorts:
% 10.46/4.26  
% 10.46/4.26  
% 10.46/4.26  %Background operators:
% 10.46/4.26  
% 10.46/4.26  
% 10.46/4.26  %Foreground operators:
% 10.46/4.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.46/4.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.46/4.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.46/4.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.46/4.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.46/4.26  tff('#skF_5', type, '#skF_5': $i).
% 10.46/4.26  tff('#skF_3', type, '#skF_3': $i).
% 10.46/4.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.46/4.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.46/4.26  tff('#skF_4', type, '#skF_4': $i).
% 10.46/4.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.46/4.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.46/4.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.46/4.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.46/4.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.46/4.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.46/4.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.46/4.26  
% 10.46/4.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.46/4.27  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.46/4.27  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.46/4.27  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 10.46/4.27  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.46/4.27  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.46/4.27  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.46/4.27  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.46/4.27  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.46/4.27  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_xboole_1)).
% 10.46/4.27  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.46/4.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.46/4.27  tff(c_83, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.46/4.27  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.46/4.27  tff(c_92, plain, (![A_44, B_45]: (r1_tarski(k3_xboole_0(A_44, B_45), A_44))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 10.46/4.27  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.46/4.27  tff(c_38, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.46/4.27  tff(c_115, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.46/4.27  tff(c_16, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.46/4.27  tff(c_122, plain, (![B_50, A_14]: (r1_tarski(B_50, A_14) | ~m1_subset_1(B_50, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_115, c_16])).
% 10.46/4.27  tff(c_127, plain, (![B_52, A_53]: (r1_tarski(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(negUnitSimplification, [status(thm)], [c_38, c_122])).
% 10.46/4.27  tff(c_144, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_127])).
% 10.46/4.27  tff(c_153, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.46/4.27  tff(c_164, plain, (![A_54]: (r1_tarski(A_54, '#skF_3') | ~r1_tarski(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_144, c_153])).
% 10.46/4.27  tff(c_18, plain, (![C_18, A_14]: (r2_hidden(C_18, k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.46/4.27  tff(c_71, plain, (![B_40, A_41]: (m1_subset_1(B_40, A_41) | ~r2_hidden(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.46/4.27  tff(c_74, plain, (![C_18, A_14]: (m1_subset_1(C_18, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(resolution, [status(thm)], [c_18, c_71])).
% 10.46/4.27  tff(c_77, plain, (![C_18, A_14]: (m1_subset_1(C_18, k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(negUnitSimplification, [status(thm)], [c_38, c_74])).
% 10.46/4.27  tff(c_176, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.46/4.27  tff(c_894, plain, (![A_116, C_117]: (k4_xboole_0(A_116, C_117)=k3_subset_1(A_116, C_117) | ~r1_tarski(C_117, A_116))), inference(resolution, [status(thm)], [c_77, c_176])).
% 10.46/4.27  tff(c_3333, plain, (![A_219]: (k4_xboole_0('#skF_3', A_219)=k3_subset_1('#skF_3', A_219) | ~r1_tarski(A_219, '#skF_4'))), inference(resolution, [status(thm)], [c_164, c_894])).
% 10.46/4.27  tff(c_17307, plain, (![B_527]: (k4_xboole_0('#skF_3', k3_xboole_0('#skF_4', B_527))=k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_527)))), inference(resolution, [status(thm)], [c_92, c_3333])).
% 10.46/4.27  tff(c_193, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_176])).
% 10.46/4.27  tff(c_1269, plain, (![A_128, D_129, B_130, C_131]: (r1_tarski(k4_xboole_0(A_128, D_129), k4_xboole_0(B_130, C_131)) | ~r1_tarski(C_131, D_129) | ~r1_tarski(A_128, B_130))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.46/4.27  tff(c_1308, plain, (![B_130, C_131]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0(B_130, C_131)) | ~r1_tarski(C_131, '#skF_4') | ~r1_tarski('#skF_3', B_130))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1269])).
% 10.46/4.27  tff(c_17437, plain, (![B_527]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_527))) | ~r1_tarski(k3_xboole_0('#skF_4', B_527), '#skF_4') | ~r1_tarski('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_17307, c_1308])).
% 10.46/4.27  tff(c_17513, plain, (![B_527]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_527))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92, c_17437])).
% 10.46/4.27  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.46/4.27  tff(c_314, plain, (![A_69, B_70, C_71]: (k9_subset_1(A_69, B_70, C_71)=k3_xboole_0(B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.46/4.27  tff(c_326, plain, (![B_70]: (k9_subset_1('#skF_3', B_70, '#skF_5')=k3_xboole_0(B_70, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_314])).
% 10.46/4.27  tff(c_42, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.46/4.27  tff(c_328, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_42])).
% 10.46/4.27  tff(c_17974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17513, c_328])).
% 10.46/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.46/4.27  
% 10.46/4.27  Inference rules
% 10.46/4.27  ----------------------
% 10.46/4.27  #Ref     : 0
% 10.46/4.27  #Sup     : 4348
% 10.46/4.27  #Fact    : 0
% 10.46/4.27  #Define  : 0
% 10.46/4.27  #Split   : 7
% 10.46/4.27  #Chain   : 0
% 10.46/4.27  #Close   : 0
% 10.46/4.27  
% 10.46/4.27  Ordering : KBO
% 10.46/4.27  
% 10.46/4.27  Simplification rules
% 10.46/4.27  ----------------------
% 10.46/4.27  #Subsume      : 377
% 10.46/4.27  #Demod        : 985
% 10.46/4.27  #Tautology    : 529
% 10.46/4.27  #SimpNegUnit  : 12
% 10.46/4.27  #BackRed      : 9
% 10.46/4.27  
% 10.46/4.27  #Partial instantiations: 0
% 10.46/4.27  #Strategies tried      : 1
% 10.46/4.27  
% 10.46/4.27  Timing (in seconds)
% 10.46/4.27  ----------------------
% 10.58/4.28  Preprocessing        : 0.31
% 10.58/4.28  Parsing              : 0.16
% 10.58/4.28  CNF conversion       : 0.02
% 10.58/4.28  Main loop            : 3.21
% 10.58/4.28  Inferencing          : 0.60
% 10.58/4.28  Reduction            : 1.33
% 10.58/4.28  Demodulation         : 1.11
% 10.58/4.28  BG Simplification    : 0.09
% 10.58/4.28  Subsumption          : 0.96
% 10.58/4.28  Abstraction          : 0.11
% 10.58/4.28  MUC search           : 0.00
% 10.58/4.28  Cooper               : 0.00
% 10.58/4.28  Total                : 3.54
% 10.58/4.28  Index Insertion      : 0.00
% 10.58/4.28  Index Deletion       : 0.00
% 10.58/4.28  Index Matching       : 0.00
% 10.58/4.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
