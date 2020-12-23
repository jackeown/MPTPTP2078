%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 120 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 330 expanded)
%              Number of equality atoms :    4 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( v1_funct_1(k7_relat_1(A_39,B_40))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k7_relat_1(A_39,B_40))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,(
    ! [C_62,B_63,A_64] :
      ( k1_funct_1(k7_relat_1(C_62,B_63),A_64) = k1_funct_1(C_62,A_64)
      | ~ r2_hidden(A_64,B_63)
      | ~ v1_funct_1(C_62)
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [B_42,A_41] :
      ( r2_hidden(k1_funct_1(B_42,A_41),k2_relat_1(B_42))
      | ~ r2_hidden(A_41,k1_relat_1(B_42))
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1199,plain,(
    ! [C_176,A_177,B_178] :
      ( r2_hidden(k1_funct_1(C_176,A_177),k2_relat_1(k7_relat_1(C_176,B_178)))
      | ~ r2_hidden(A_177,k1_relat_1(k7_relat_1(C_176,B_178)))
      | ~ v1_funct_1(k7_relat_1(C_176,B_178))
      | ~ v1_relat_1(k7_relat_1(C_176,B_178))
      | ~ r2_hidden(A_177,B_178)
      | ~ v1_funct_1(C_176)
      | ~ v1_relat_1(C_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_40,plain,(
    ~ r2_hidden(k1_funct_1('#skF_11','#skF_9'),k2_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1202,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10')))
    | ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_1199,c_40])).

tff(c_1214,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10')))
    | ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_1202])).

tff(c_1215,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1214])).

tff(c_1218,plain,
    ( ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_1215])).

tff(c_1222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1218])).

tff(c_1224,plain,(
    v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1214])).

tff(c_20,plain,(
    ! [C_35,A_20] :
      ( r2_hidden(k4_tarski(C_35,'#skF_8'(A_20,k1_relat_1(A_20),C_35)),A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [D_83,E_84,A_85,B_86] :
      ( r2_hidden(k4_tarski(D_83,E_84),k7_relat_1(A_85,B_86))
      | ~ r2_hidden(k4_tarski(D_83,E_84),A_85)
      | ~ r2_hidden(D_83,B_86)
      | ~ v1_relat_1(k7_relat_1(A_85,B_86))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k1_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(C_35,D_38),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_182,plain,(
    ! [D_91,A_92,B_93,E_94] :
      ( r2_hidden(D_91,k1_relat_1(k7_relat_1(A_92,B_93)))
      | ~ r2_hidden(k4_tarski(D_91,E_94),A_92)
      | ~ r2_hidden(D_91,B_93)
      | ~ v1_relat_1(k7_relat_1(A_92,B_93))
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_132,c_22])).

tff(c_194,plain,(
    ! [C_35,A_20,B_93] :
      ( r2_hidden(C_35,k1_relat_1(k7_relat_1(A_20,B_93)))
      | ~ r2_hidden(C_35,B_93)
      | ~ v1_relat_1(k7_relat_1(A_20,B_93))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_20,c_182])).

tff(c_1223,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1214])).

tff(c_1230,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_1233,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_194,c_1230])).

tff(c_1237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_1224,c_42,c_1233])).

tff(c_1238,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1242,plain,
    ( ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_1238])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.70  
% 3.81/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.70  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 3.81/1.70  
% 3.81/1.70  %Foreground sorts:
% 3.81/1.70  
% 3.81/1.70  
% 3.81/1.70  %Background operators:
% 3.81/1.70  
% 3.81/1.70  
% 3.81/1.70  %Foreground operators:
% 3.81/1.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.81/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.81/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.70  tff('#skF_11', type, '#skF_11': $i).
% 3.81/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.81/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.81/1.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.81/1.70  tff('#skF_10', type, '#skF_10': $i).
% 3.81/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.81/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.81/1.70  tff('#skF_9', type, '#skF_9': $i).
% 3.81/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.81/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.81/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.70  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.81/1.70  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.81/1.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.81/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.70  
% 3.81/1.71  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 3.81/1.71  tff(f_55, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.81/1.71  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 3.81/1.71  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.81/1.71  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.81/1.71  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 3.81/1.71  tff(c_48, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.81/1.71  tff(c_46, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.81/1.71  tff(c_32, plain, (![A_39, B_40]: (v1_funct_1(k7_relat_1(A_39, B_40)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.71  tff(c_44, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.81/1.71  tff(c_34, plain, (![A_39, B_40]: (v1_relat_1(k7_relat_1(A_39, B_40)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.71  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.81/1.71  tff(c_60, plain, (![C_62, B_63, A_64]: (k1_funct_1(k7_relat_1(C_62, B_63), A_64)=k1_funct_1(C_62, A_64) | ~r2_hidden(A_64, B_63) | ~v1_funct_1(C_62) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.81/1.71  tff(c_36, plain, (![B_42, A_41]: (r2_hidden(k1_funct_1(B_42, A_41), k2_relat_1(B_42)) | ~r2_hidden(A_41, k1_relat_1(B_42)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.81/1.71  tff(c_1199, plain, (![C_176, A_177, B_178]: (r2_hidden(k1_funct_1(C_176, A_177), k2_relat_1(k7_relat_1(C_176, B_178))) | ~r2_hidden(A_177, k1_relat_1(k7_relat_1(C_176, B_178))) | ~v1_funct_1(k7_relat_1(C_176, B_178)) | ~v1_relat_1(k7_relat_1(C_176, B_178)) | ~r2_hidden(A_177, B_178) | ~v1_funct_1(C_176) | ~v1_relat_1(C_176))), inference(superposition, [status(thm), theory('equality')], [c_60, c_36])).
% 3.81/1.71  tff(c_40, plain, (~r2_hidden(k1_funct_1('#skF_11', '#skF_9'), k2_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.81/1.71  tff(c_1202, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10'))) | ~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_1199, c_40])).
% 3.81/1.71  tff(c_1214, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10'))) | ~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_1202])).
% 3.81/1.71  tff(c_1215, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitLeft, [status(thm)], [c_1214])).
% 3.81/1.71  tff(c_1218, plain, (~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_34, c_1215])).
% 3.81/1.71  tff(c_1222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1218])).
% 3.81/1.71  tff(c_1224, plain, (v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_1214])).
% 3.81/1.71  tff(c_20, plain, (![C_35, A_20]: (r2_hidden(k4_tarski(C_35, '#skF_8'(A_20, k1_relat_1(A_20), C_35)), A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.71  tff(c_132, plain, (![D_83, E_84, A_85, B_86]: (r2_hidden(k4_tarski(D_83, E_84), k7_relat_1(A_85, B_86)) | ~r2_hidden(k4_tarski(D_83, E_84), A_85) | ~r2_hidden(D_83, B_86) | ~v1_relat_1(k7_relat_1(A_85, B_86)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.71  tff(c_22, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k1_relat_1(A_20)) | ~r2_hidden(k4_tarski(C_35, D_38), A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.71  tff(c_182, plain, (![D_91, A_92, B_93, E_94]: (r2_hidden(D_91, k1_relat_1(k7_relat_1(A_92, B_93))) | ~r2_hidden(k4_tarski(D_91, E_94), A_92) | ~r2_hidden(D_91, B_93) | ~v1_relat_1(k7_relat_1(A_92, B_93)) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_132, c_22])).
% 3.81/1.71  tff(c_194, plain, (![C_35, A_20, B_93]: (r2_hidden(C_35, k1_relat_1(k7_relat_1(A_20, B_93))) | ~r2_hidden(C_35, B_93) | ~v1_relat_1(k7_relat_1(A_20, B_93)) | ~v1_relat_1(A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(resolution, [status(thm)], [c_20, c_182])).
% 3.81/1.71  tff(c_1223, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(splitRight, [status(thm)], [c_1214])).
% 3.81/1.71  tff(c_1230, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(splitLeft, [status(thm)], [c_1223])).
% 3.81/1.71  tff(c_1233, plain, (~r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11') | ~r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_194, c_1230])).
% 3.81/1.71  tff(c_1237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_1224, c_42, c_1233])).
% 3.81/1.71  tff(c_1238, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_1223])).
% 3.81/1.71  tff(c_1242, plain, (~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_1238])).
% 3.81/1.71  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1242])).
% 3.81/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.71  
% 3.81/1.71  Inference rules
% 3.81/1.71  ----------------------
% 3.81/1.71  #Ref     : 0
% 3.81/1.71  #Sup     : 270
% 3.81/1.71  #Fact    : 0
% 3.81/1.71  #Define  : 0
% 3.81/1.71  #Split   : 2
% 3.81/1.71  #Chain   : 0
% 3.81/1.71  #Close   : 0
% 3.81/1.71  
% 3.81/1.71  Ordering : KBO
% 3.81/1.71  
% 3.81/1.71  Simplification rules
% 3.81/1.71  ----------------------
% 3.81/1.71  #Subsume      : 32
% 3.81/1.71  #Demod        : 12
% 3.81/1.71  #Tautology    : 31
% 3.81/1.71  #SimpNegUnit  : 0
% 3.81/1.71  #BackRed      : 0
% 3.81/1.71  
% 3.81/1.71  #Partial instantiations: 0
% 3.81/1.71  #Strategies tried      : 1
% 3.81/1.71  
% 3.81/1.71  Timing (in seconds)
% 3.81/1.71  ----------------------
% 3.81/1.72  Preprocessing        : 0.31
% 3.81/1.72  Parsing              : 0.16
% 3.81/1.72  CNF conversion       : 0.03
% 3.81/1.72  Main loop            : 0.57
% 3.81/1.72  Inferencing          : 0.21
% 3.81/1.72  Reduction            : 0.13
% 3.81/1.72  Demodulation         : 0.09
% 3.81/1.72  BG Simplification    : 0.03
% 3.81/1.72  Subsumption          : 0.16
% 3.81/1.72  Abstraction          : 0.03
% 3.81/1.72  MUC search           : 0.00
% 3.81/1.72  Cooper               : 0.00
% 3.81/1.72  Total                : 0.91
% 3.81/1.72  Index Insertion      : 0.00
% 3.81/1.72  Index Deletion       : 0.00
% 3.81/1.72  Index Matching       : 0.00
% 3.81/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
