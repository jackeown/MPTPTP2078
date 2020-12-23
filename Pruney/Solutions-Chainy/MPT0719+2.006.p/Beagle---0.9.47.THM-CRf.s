%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   51 (  91 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 135 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_45,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_36,C_37,B_38] :
      ( ~ r2_hidden(A_36,C_37)
      | ~ r1_xboole_0(k2_tarski(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_12,plain,(
    ! [A_11] :
      ( v1_relat_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_16,plain,(
    ! [A_12] :
      ( v1_funct_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_16])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_40] :
      ( k1_relat_1(k6_relat_1(A_40)) = A_40
      | ~ v1_funct_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,
    ( k1_relat_1(k6_relat_1(k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_1(k6_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_84,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_78,c_14,c_14,c_82])).

tff(c_111,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),k1_relat_1(B_45))
      | v5_funct_1(B_45,A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_111])).

tff(c_120,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_78,c_117])).

tff(c_122,plain,(
    ! [A_46] :
      ( v5_funct_1(k1_xboole_0,A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_120])).

tff(c_32,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_125,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_32])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.91/1.17  
% 1.91/1.17  %Foreground sorts:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Background operators:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Foreground operators:
% 1.91/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.17  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.91/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.17  
% 1.91/1.18  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.91/1.18  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.18  tff(f_40, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.91/1.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.91/1.18  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.91/1.18  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.91/1.18  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.91/1.18  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 1.91/1.18  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.91/1.18  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.18  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.18  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.18  tff(c_59, plain, (![A_36, C_37, B_38]: (~r2_hidden(A_36, C_37) | ~r1_xboole_0(k2_tarski(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.18  tff(c_64, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_59])).
% 1.91/1.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.18  tff(c_65, plain, (![A_39]: (~r2_hidden(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_59])).
% 1.91/1.18  tff(c_70, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_65])).
% 1.91/1.18  tff(c_12, plain, (![A_11]: (v1_relat_1(A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.18  tff(c_77, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_12])).
% 1.91/1.18  tff(c_16, plain, (![A_12]: (v1_funct_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.18  tff(c_78, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_16])).
% 1.91/1.18  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.18  tff(c_79, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40 | ~v1_funct_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.91/1.18  tff(c_82, plain, (k1_relat_1(k6_relat_1(k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(k6_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_79])).
% 1.91/1.18  tff(c_84, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_78, c_14, c_14, c_82])).
% 1.91/1.18  tff(c_111, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), k1_relat_1(B_45)) | v5_funct_1(B_45, A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.18  tff(c_117, plain, (![A_44]: (r2_hidden('#skF_2'(A_44, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_84, c_111])).
% 1.91/1.18  tff(c_120, plain, (![A_44]: (r2_hidden('#skF_2'(A_44, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_78, c_117])).
% 1.91/1.18  tff(c_122, plain, (![A_46]: (v5_funct_1(k1_xboole_0, A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(negUnitSimplification, [status(thm)], [c_64, c_120])).
% 1.91/1.18  tff(c_32, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.18  tff(c_125, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_32])).
% 1.91/1.18  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_125])).
% 1.91/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  Inference rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Ref     : 0
% 1.91/1.18  #Sup     : 19
% 1.91/1.18  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 0
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 1
% 1.91/1.19  #Demod        : 22
% 1.91/1.19  #Tautology    : 9
% 1.91/1.19  #SimpNegUnit  : 3
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.19  Preprocessing        : 0.31
% 1.91/1.19  Parsing              : 0.15
% 1.91/1.19  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.13
% 1.91/1.19  Inferencing          : 0.05
% 1.91/1.19  Reduction            : 0.04
% 1.91/1.19  Demodulation         : 0.03
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.02
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.46
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
