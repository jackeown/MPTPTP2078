%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 239 expanded)
%              Number of leaves         :   22 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 (1016 expanded)
%              Number of equality atoms :   38 ( 290 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => ( v2_funct_1(C)
        <=> ! [D,E] :
              ( ( r2_hidden(D,A)
                & r2_hidden(E,A)
                & k1_funct_1(C,D) = k1_funct_1(C,E) )
             => D = E ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

tff(c_24,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    ! [D_33,C_34,B_35,A_36] :
      ( k1_funct_1(k2_funct_1(D_33),k1_funct_1(D_33,C_34)) = C_34
      | k1_xboole_0 = B_35
      | ~ r2_hidden(C_34,A_36)
      | ~ v2_funct_1(D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_36,B_35)))
      | ~ v1_funct_2(D_33,A_36,B_35)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    ! [D_37,B_38] :
      ( k1_funct_1(k2_funct_1(D_37),k1_funct_1(D_37,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_38
      | ~ v2_funct_1(D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_38)))
      | ~ v1_funct_2(D_37,'#skF_3',B_38)
      | ~ v1_funct_1(D_37) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_78,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_75])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_18,plain,(
    ! [E_9,D_8,C_3,B_2] :
      ( E_9 = D_8
      | k1_funct_1(C_3,E_9) != k1_funct_1(C_3,D_8)
      | ~ r2_hidden(E_9,k1_xboole_0)
      | ~ r2_hidden(D_8,k1_xboole_0)
      | ~ v2_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [E_63,D_64,C_65,B_66] :
      ( E_63 = D_64
      | k1_funct_1(C_65,E_63) != k1_funct_1(C_65,D_64)
      | ~ r2_hidden(E_63,'#skF_3')
      | ~ r2_hidden(D_64,'#skF_3')
      | ~ v2_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_66)))
      | ~ v1_funct_2(C_65,'#skF_3',B_66)
      | ~ v1_funct_1(C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_79,c_79,c_18])).

tff(c_172,plain,(
    ! [D_64,B_66] :
      ( D_64 = '#skF_5'
      | k1_funct_1('#skF_4',D_64) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5','#skF_3')
      | ~ r2_hidden(D_64,'#skF_3')
      | ~ v2_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_66)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_66)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_170])).

tff(c_176,plain,(
    ! [D_64,B_66] :
      ( D_64 = '#skF_5'
      | k1_funct_1('#skF_4',D_64) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(D_64,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_66)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_172])).

tff(c_180,plain,(
    ! [B_67] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_67)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_67) ) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_183,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_183])).

tff(c_189,plain,(
    ! [D_68] :
      ( D_68 = '#skF_5'
      | k1_funct_1('#skF_4',D_68) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(D_68,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_192,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_189])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_192])).

tff(c_201,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_200,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_213,plain,(
    ! [D_72,B_73] :
      ( k1_funct_1(k2_funct_1(D_72),k1_funct_1(D_72,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_73
      | ~ v2_funct_1(D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_73)))
      | ~ v1_funct_2(D_72,'#skF_3',B_73)
      | ~ v1_funct_1(D_72) ) ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_215,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_213])).

tff(c_218,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_200,c_26,c_215])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_24,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.15/1.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.15/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.29  
% 2.15/1.30  tff(f_78, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.15/1.30  tff(f_60, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.15/1.30  tff(f_46, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (v2_funct_1(C) <=> (![D, E]: (((r2_hidden(D, A) & r2_hidden(E, A)) & (k1_funct_1(C, D) = k1_funct_1(C, E))) => (D = E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 2.15/1.30  tff(c_24, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_28, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_32, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_26, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_66, plain, (![D_33, C_34, B_35, A_36]: (k1_funct_1(k2_funct_1(D_33), k1_funct_1(D_33, C_34))=C_34 | k1_xboole_0=B_35 | ~r2_hidden(C_34, A_36) | ~v2_funct_1(D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_36, B_35))) | ~v1_funct_2(D_33, A_36, B_35) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.30  tff(c_73, plain, (![D_37, B_38]: (k1_funct_1(k2_funct_1(D_37), k1_funct_1(D_37, '#skF_6'))='#skF_6' | k1_xboole_0=B_38 | ~v2_funct_1(D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_38))) | ~v1_funct_2(D_37, '#skF_3', B_38) | ~v1_funct_1(D_37))), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.15/1.30  tff(c_75, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.15/1.30  tff(c_78, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_75])).
% 2.15/1.30  tff(c_79, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_78])).
% 2.15/1.30  tff(c_18, plain, (![E_9, D_8, C_3, B_2]: (E_9=D_8 | k1_funct_1(C_3, E_9)!=k1_funct_1(C_3, D_8) | ~r2_hidden(E_9, k1_xboole_0) | ~r2_hidden(D_8, k1_xboole_0) | ~v2_funct_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.30  tff(c_170, plain, (![E_63, D_64, C_65, B_66]: (E_63=D_64 | k1_funct_1(C_65, E_63)!=k1_funct_1(C_65, D_64) | ~r2_hidden(E_63, '#skF_3') | ~r2_hidden(D_64, '#skF_3') | ~v2_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_66))) | ~v1_funct_2(C_65, '#skF_3', B_66) | ~v1_funct_1(C_65))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_79, c_79, c_18])).
% 2.15/1.30  tff(c_172, plain, (![D_64, B_66]: (D_64='#skF_5' | k1_funct_1('#skF_4', D_64)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden(D_64, '#skF_3') | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_66))) | ~v1_funct_2('#skF_4', '#skF_3', B_66) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_170])).
% 2.15/1.30  tff(c_176, plain, (![D_64, B_66]: (D_64='#skF_5' | k1_funct_1('#skF_4', D_64)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(D_64, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_66))) | ~v1_funct_2('#skF_4', '#skF_3', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_172])).
% 2.15/1.30  tff(c_180, plain, (![B_67]: (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_67))) | ~v1_funct_2('#skF_4', '#skF_3', B_67))), inference(splitLeft, [status(thm)], [c_176])).
% 2.15/1.30  tff(c_183, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_180])).
% 2.15/1.30  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_183])).
% 2.15/1.30  tff(c_189, plain, (![D_68]: (D_68='#skF_5' | k1_funct_1('#skF_4', D_68)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(D_68, '#skF_3'))), inference(splitRight, [status(thm)], [c_176])).
% 2.15/1.30  tff(c_192, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_28, c_189])).
% 2.15/1.30  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_192])).
% 2.15/1.30  tff(c_201, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_78])).
% 2.15/1.30  tff(c_200, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_78])).
% 2.15/1.30  tff(c_213, plain, (![D_72, B_73]: (k1_funct_1(k2_funct_1(D_72), k1_funct_1(D_72, '#skF_5'))='#skF_5' | k1_xboole_0=B_73 | ~v2_funct_1(D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_73))) | ~v1_funct_2(D_72, '#skF_3', B_73) | ~v1_funct_1(D_72))), inference(resolution, [status(thm)], [c_30, c_66])).
% 2.15/1.30  tff(c_215, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_213])).
% 2.15/1.30  tff(c_218, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_200, c_26, c_215])).
% 2.15/1.30  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_24, c_218])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 1
% 2.15/1.30  #Sup     : 29
% 2.15/1.30  #Fact    : 0
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 2
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Subsume      : 0
% 2.15/1.30  #Demod        : 85
% 2.15/1.30  #Tautology    : 21
% 2.15/1.30  #SimpNegUnit  : 3
% 2.15/1.30  #BackRed      : 9
% 2.15/1.30  
% 2.15/1.30  #Partial instantiations: 0
% 2.15/1.30  #Strategies tried      : 1
% 2.15/1.30  
% 2.15/1.30  Timing (in seconds)
% 2.15/1.30  ----------------------
% 2.15/1.30  Preprocessing        : 0.31
% 2.15/1.30  Parsing              : 0.16
% 2.15/1.30  CNF conversion       : 0.03
% 2.15/1.30  Main loop            : 0.20
% 2.15/1.30  Inferencing          : 0.07
% 2.15/1.30  Reduction            : 0.07
% 2.15/1.30  Demodulation         : 0.05
% 2.15/1.30  BG Simplification    : 0.02
% 2.15/1.30  Subsumption          : 0.03
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.55
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
