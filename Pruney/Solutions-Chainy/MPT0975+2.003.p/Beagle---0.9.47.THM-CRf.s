%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 151 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_relat_1(E)
              & v1_funct_1(E) )
           => ( r2_hidden(C,A)
             => ( B = k1_xboole_0
                | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    ! [B_19,A_20] :
      ( v1_relat_1(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_45,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_65,plain,(
    ! [B_34,A_35,C_36] :
      ( k1_xboole_0 = B_34
      | k1_relset_1(A_35,B_34,C_36) = A_35
      | ~ v1_funct_2(C_36,A_35,B_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_71,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_49,c_68])).

tff(c_72,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_71])).

tff(c_82,plain,(
    ! [B_37,C_38,A_39] :
      ( k1_funct_1(k5_relat_1(B_37,C_38),A_39) = k1_funct_1(C_38,k1_funct_1(B_37,A_39))
      | ~ r2_hidden(A_39,k1_relat_1(B_37))
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [C_38,A_39] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_38),A_39) = k1_funct_1(C_38,k1_funct_1('#skF_4',A_39))
      | ~ r2_hidden(A_39,'#skF_1')
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_82])).

tff(c_87,plain,(
    ! [C_40,A_41] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_40),A_41) = k1_funct_1(C_40,k1_funct_1('#skF_4',A_41))
      | ~ r2_hidden(A_41,'#skF_1')
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_84])).

tff(c_22,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_93,plain,
    ( ~ r2_hidden('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_22])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.97/1.20  
% 1.97/1.20  %Foreground sorts:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Background operators:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Foreground operators:
% 1.97/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.97/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.97/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.20  
% 1.97/1.21  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 1.97/1.21  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.97/1.21  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.97/1.21  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.97/1.21  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.97/1.21  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 1.97/1.21  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.97/1.21  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_38, plain, (![B_19, A_20]: (v1_relat_1(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.21  tff(c_41, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 1.97/1.21  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_41])).
% 1.97/1.21  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_45, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.21  tff(c_49, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_45])).
% 1.97/1.21  tff(c_65, plain, (![B_34, A_35, C_36]: (k1_xboole_0=B_34 | k1_relset_1(A_35, B_34, C_36)=A_35 | ~v1_funct_2(C_36, A_35, B_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.97/1.21  tff(c_68, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_65])).
% 1.97/1.21  tff(c_71, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_49, c_68])).
% 1.97/1.21  tff(c_72, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_24, c_71])).
% 1.97/1.21  tff(c_82, plain, (![B_37, C_38, A_39]: (k1_funct_1(k5_relat_1(B_37, C_38), A_39)=k1_funct_1(C_38, k1_funct_1(B_37, A_39)) | ~r2_hidden(A_39, k1_relat_1(B_37)) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.21  tff(c_84, plain, (![C_38, A_39]: (k1_funct_1(k5_relat_1('#skF_4', C_38), A_39)=k1_funct_1(C_38, k1_funct_1('#skF_4', A_39)) | ~r2_hidden(A_39, '#skF_1') | ~v1_funct_1(C_38) | ~v1_relat_1(C_38) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_82])).
% 1.97/1.21  tff(c_87, plain, (![C_40, A_41]: (k1_funct_1(k5_relat_1('#skF_4', C_40), A_41)=k1_funct_1(C_40, k1_funct_1('#skF_4', A_41)) | ~r2_hidden(A_41, '#skF_1') | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_84])).
% 1.97/1.21  tff(c_22, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.21  tff(c_93, plain, (~r2_hidden('#skF_3', '#skF_1') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_87, c_22])).
% 1.97/1.21  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_93])).
% 1.97/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  Inference rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Ref     : 0
% 1.97/1.21  #Sup     : 14
% 1.97/1.21  #Fact    : 0
% 1.97/1.21  #Define  : 0
% 1.97/1.21  #Split   : 0
% 1.97/1.21  #Chain   : 0
% 1.97/1.21  #Close   : 0
% 1.97/1.21  
% 1.97/1.21  Ordering : KBO
% 1.97/1.21  
% 1.97/1.21  Simplification rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Subsume      : 0
% 1.97/1.21  #Demod        : 11
% 1.97/1.21  #Tautology    : 8
% 1.97/1.21  #SimpNegUnit  : 2
% 1.97/1.21  #BackRed      : 1
% 1.97/1.21  
% 1.97/1.21  #Partial instantiations: 0
% 1.97/1.21  #Strategies tried      : 1
% 1.97/1.21  
% 1.97/1.21  Timing (in seconds)
% 1.97/1.21  ----------------------
% 1.97/1.22  Preprocessing        : 0.29
% 1.97/1.22  Parsing              : 0.15
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.13
% 1.97/1.22  Inferencing          : 0.05
% 1.97/1.22  Reduction            : 0.04
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.02
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.45
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
