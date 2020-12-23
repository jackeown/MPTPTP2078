%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:05 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 ( 132 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_59,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_86,plain,(
    ! [B_49,A_50,C_51] :
      ( k1_xboole_0 = B_49
      | k1_relset_1(A_50,B_49,C_51) = A_50
      | ~ v1_funct_2(C_51,A_50,B_49)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_92,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_63,c_89])).

tff(c_93,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_92])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_47,plain,(
    ! [C_25,B_26,A_27] :
      ( v5_relat_1(C_25,B_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_27,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_68,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(k1_funct_1(B_38,A_39),k2_relat_1(B_38))
      | ~ r2_hidden(A_39,k1_relat_1(B_38))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,k2_relat_1(B_7))
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [B_46,A_47,A_48] :
      ( r2_hidden(k1_funct_1(B_46,A_47),A_48)
      | ~ v5_relat_1(B_46,A_48)
      | ~ r2_hidden(A_47,k1_relat_1(B_46))
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_68,c_6])).

tff(c_28,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_81,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_28])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_51,c_81])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_85])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.95/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.95/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.21  
% 1.95/1.23  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.95/1.23  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.95/1.23  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.95/1.23  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.95/1.23  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.95/1.23  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.95/1.23  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 1.95/1.23  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 1.95/1.23  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.95/1.23  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.95/1.23  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.95/1.23  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.95/1.23  tff(c_59, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.23  tff(c_63, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_59])).
% 1.95/1.23  tff(c_86, plain, (![B_49, A_50, C_51]: (k1_xboole_0=B_49 | k1_relset_1(A_50, B_49, C_51)=A_50 | ~v1_funct_2(C_51, A_50, B_49) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.95/1.23  tff(c_89, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_86])).
% 1.95/1.23  tff(c_92, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_63, c_89])).
% 1.95/1.23  tff(c_93, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_92])).
% 1.95/1.23  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.23  tff(c_40, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.23  tff(c_43, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_40])).
% 1.95/1.23  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_43])).
% 1.95/1.23  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.95/1.23  tff(c_47, plain, (![C_25, B_26, A_27]: (v5_relat_1(C_25, B_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_27, B_26))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.23  tff(c_51, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_47])).
% 1.95/1.23  tff(c_68, plain, (![B_38, A_39]: (r2_hidden(k1_funct_1(B_38, A_39), k2_relat_1(B_38)) | ~r2_hidden(A_39, k1_relat_1(B_38)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.23  tff(c_6, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, k2_relat_1(B_7)) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.23  tff(c_75, plain, (![B_46, A_47, A_48]: (r2_hidden(k1_funct_1(B_46, A_47), A_48) | ~v5_relat_1(B_46, A_48) | ~r2_hidden(A_47, k1_relat_1(B_46)) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_68, c_6])).
% 1.95/1.23  tff(c_28, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.95/1.23  tff(c_81, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_75, c_28])).
% 1.95/1.23  tff(c_85, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_51, c_81])).
% 1.95/1.23  tff(c_94, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_85])).
% 1.95/1.23  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_94])).
% 1.95/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  Inference rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Ref     : 0
% 1.95/1.23  #Sup     : 10
% 1.95/1.23  #Fact    : 0
% 1.95/1.23  #Define  : 0
% 1.95/1.23  #Split   : 0
% 1.95/1.23  #Chain   : 0
% 1.95/1.23  #Close   : 0
% 1.95/1.23  
% 1.95/1.23  Ordering : KBO
% 1.95/1.23  
% 1.95/1.23  Simplification rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Subsume      : 0
% 1.95/1.23  #Demod        : 9
% 1.95/1.23  #Tautology    : 2
% 1.95/1.23  #SimpNegUnit  : 1
% 1.95/1.23  #BackRed      : 2
% 1.95/1.23  
% 1.95/1.23  #Partial instantiations: 0
% 1.95/1.23  #Strategies tried      : 1
% 1.95/1.23  
% 1.95/1.23  Timing (in seconds)
% 1.95/1.23  ----------------------
% 1.95/1.23  Preprocessing        : 0.32
% 1.95/1.23  Parsing              : 0.17
% 1.95/1.23  CNF conversion       : 0.02
% 1.95/1.23  Main loop            : 0.13
% 1.95/1.23  Inferencing          : 0.05
% 1.95/1.23  Reduction            : 0.04
% 1.95/1.23  Demodulation         : 0.03
% 1.95/1.23  BG Simplification    : 0.01
% 1.95/1.23  Subsumption          : 0.02
% 1.95/1.23  Abstraction          : 0.01
% 1.95/1.23  MUC search           : 0.00
% 1.95/1.23  Cooper               : 0.00
% 1.95/1.23  Total                : 0.49
% 1.95/1.23  Index Insertion      : 0.00
% 1.95/1.23  Index Deletion       : 0.00
% 1.95/1.23  Index Matching       : 0.00
% 1.95/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
