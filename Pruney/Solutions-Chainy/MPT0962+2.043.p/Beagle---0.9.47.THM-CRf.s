%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 126 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 344 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_282,plain,(
    ! [C_76,A_77,B_78] :
      ( m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ r1_tarski(k2_relat_1(C_76),B_78)
      | ~ r1_tarski(k1_relat_1(C_76),A_77)
      | ~ v1_relat_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32])).

tff(c_71,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_92,plain,(
    ! [C_32,A_33,B_34] :
      ( m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ r1_tarski(k2_relat_1(C_32),B_34)
      | ~ r1_tarski(k1_relat_1(C_32),A_33)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_4,B_5,C_6] :
      ( k1_relset_1(A_4,B_5,C_6) = k1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ r1_tarski(k2_relat_1(C_37),B_36)
      | ~ r1_tarski(k1_relat_1(C_37),A_35)
      | ~ v1_relat_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_92,c_10])).

tff(c_120,plain,(
    ! [A_35] :
      ( k1_relset_1(A_35,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_35)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_128,plain,(
    ! [A_38] :
      ( k1_relset_1(A_38,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_120])).

tff(c_133,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_12,plain,(
    ! [C_9,A_7,B_8] :
      ( m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ r1_tarski(k2_relat_1(C_9),B_8)
      | ~ r1_tarski(k1_relat_1(C_9),A_7)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [B_39,C_40,A_41] :
      ( k1_xboole_0 = B_39
      | v1_funct_2(C_40,A_41,B_39)
      | k1_relset_1(A_41,B_39,C_40) != A_41
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_213,plain,(
    ! [B_59,C_60,A_61] :
      ( k1_xboole_0 = B_59
      | v1_funct_2(C_60,A_61,B_59)
      | k1_relset_1(A_61,B_59,C_60) != A_61
      | ~ r1_tarski(k2_relat_1(C_60),B_59)
      | ~ r1_tarski(k1_relat_1(C_60),A_61)
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_215,plain,(
    ! [A_61] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_61,'#skF_1')
      | k1_relset_1(A_61,'#skF_1','#skF_2') != A_61
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_61)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_213])).

tff(c_221,plain,(
    ! [A_61] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_61,'#skF_1')
      | k1_relset_1(A_61,'#skF_1','#skF_2') != A_61
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_215])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_240,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_8])).

tff(c_44,plain,(
    ! [B_16,A_17] :
      ( B_16 = A_17
      | ~ r1_tarski(B_16,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_70])).

tff(c_250,plain,(
    ! [A_62] :
      ( v1_funct_2('#skF_2',A_62,'#skF_1')
      | k1_relset_1(A_62,'#skF_1','#skF_2') != A_62
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_62) ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_254,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_250])).

tff(c_257,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_254])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_257])).

tff(c_260,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_304,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_260])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6,c_34,c_304])).

tff(c_314,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_28,plain,(
    ! [A_13] :
      ( v1_funct_2(A_13,k1_relat_1(A_13),k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_322,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_28])).

tff(c_326,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_322])).

tff(c_330,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_40])).

tff(c_331,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80),k2_relat_1(A_80))))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_334,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_331])).

tff(c_336,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_334])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.51  
% 2.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.52  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.52  
% 2.21/1.52  %Foreground sorts:
% 2.21/1.52  
% 2.21/1.52  
% 2.21/1.52  %Background operators:
% 2.21/1.52  
% 2.21/1.52  
% 2.21/1.52  %Foreground operators:
% 2.21/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.52  
% 2.36/1.53  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.36/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.53  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.36/1.53  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.36/1.53  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.36/1.53  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.36/1.53  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.36/1.53  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.53  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.53  tff(c_34, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.53  tff(c_282, plain, (![C_76, A_77, B_78]: (m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~r1_tarski(k2_relat_1(C_76), B_78) | ~r1_tarski(k1_relat_1(C_76), A_77) | ~v1_relat_1(C_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.53  tff(c_32, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.53  tff(c_40, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32])).
% 2.36/1.53  tff(c_71, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 2.36/1.53  tff(c_92, plain, (![C_32, A_33, B_34]: (m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~r1_tarski(k2_relat_1(C_32), B_34) | ~r1_tarski(k1_relat_1(C_32), A_33) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.53  tff(c_10, plain, (![A_4, B_5, C_6]: (k1_relset_1(A_4, B_5, C_6)=k1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.53  tff(c_118, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~r1_tarski(k2_relat_1(C_37), B_36) | ~r1_tarski(k1_relat_1(C_37), A_35) | ~v1_relat_1(C_37))), inference(resolution, [status(thm)], [c_92, c_10])).
% 2.36/1.53  tff(c_120, plain, (![A_35]: (k1_relset_1(A_35, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_35) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.36/1.53  tff(c_128, plain, (![A_38]: (k1_relset_1(A_38, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_38))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_120])).
% 2.36/1.53  tff(c_133, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_128])).
% 2.36/1.53  tff(c_12, plain, (![C_9, A_7, B_8]: (m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~r1_tarski(k2_relat_1(C_9), B_8) | ~r1_tarski(k1_relat_1(C_9), A_7) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.53  tff(c_138, plain, (![B_39, C_40, A_41]: (k1_xboole_0=B_39 | v1_funct_2(C_40, A_41, B_39) | k1_relset_1(A_41, B_39, C_40)!=A_41 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.53  tff(c_213, plain, (![B_59, C_60, A_61]: (k1_xboole_0=B_59 | v1_funct_2(C_60, A_61, B_59) | k1_relset_1(A_61, B_59, C_60)!=A_61 | ~r1_tarski(k2_relat_1(C_60), B_59) | ~r1_tarski(k1_relat_1(C_60), A_61) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_12, c_138])).
% 2.36/1.53  tff(c_215, plain, (![A_61]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_61, '#skF_1') | k1_relset_1(A_61, '#skF_1', '#skF_2')!=A_61 | ~r1_tarski(k1_relat_1('#skF_2'), A_61) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_213])).
% 2.36/1.53  tff(c_221, plain, (![A_61]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_61, '#skF_1') | k1_relset_1(A_61, '#skF_1', '#skF_2')!=A_61 | ~r1_tarski(k1_relat_1('#skF_2'), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_215])).
% 2.36/1.53  tff(c_223, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_221])).
% 2.36/1.53  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.53  tff(c_240, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_8])).
% 2.36/1.53  tff(c_44, plain, (![B_16, A_17]: (B_16=A_17 | ~r1_tarski(B_16, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.53  tff(c_51, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.36/1.53  tff(c_70, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_51])).
% 2.36/1.53  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_70])).
% 2.36/1.53  tff(c_250, plain, (![A_62]: (v1_funct_2('#skF_2', A_62, '#skF_1') | k1_relset_1(A_62, '#skF_1', '#skF_2')!=A_62 | ~r1_tarski(k1_relat_1('#skF_2'), A_62))), inference(splitRight, [status(thm)], [c_221])).
% 2.36/1.53  tff(c_254, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_250])).
% 2.36/1.53  tff(c_257, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_254])).
% 2.36/1.53  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_257])).
% 2.36/1.53  tff(c_260, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_40])).
% 2.36/1.53  tff(c_304, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_282, c_260])).
% 2.36/1.53  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_6, c_34, c_304])).
% 2.36/1.53  tff(c_314, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_51])).
% 2.36/1.53  tff(c_28, plain, (![A_13]: (v1_funct_2(A_13, k1_relat_1(A_13), k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.53  tff(c_322, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_314, c_28])).
% 2.36/1.53  tff(c_326, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_322])).
% 2.36/1.53  tff(c_330, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_40])).
% 2.36/1.53  tff(c_331, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80), k2_relat_1(A_80)))) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.53  tff(c_334, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_314, c_331])).
% 2.36/1.53  tff(c_336, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_334])).
% 2.36/1.53  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_336])).
% 2.36/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.53  
% 2.36/1.53  Inference rules
% 2.36/1.53  ----------------------
% 2.36/1.53  #Ref     : 0
% 2.36/1.53  #Sup     : 50
% 2.36/1.53  #Fact    : 0
% 2.36/1.53  #Define  : 0
% 2.36/1.53  #Split   : 5
% 2.36/1.53  #Chain   : 0
% 2.36/1.53  #Close   : 0
% 2.36/1.53  
% 2.36/1.53  Ordering : KBO
% 2.36/1.53  
% 2.36/1.53  Simplification rules
% 2.36/1.53  ----------------------
% 2.36/1.53  #Subsume      : 5
% 2.36/1.53  #Demod        : 70
% 2.36/1.53  #Tautology    : 21
% 2.36/1.53  #SimpNegUnit  : 2
% 2.36/1.53  #BackRed      : 19
% 2.36/1.53  
% 2.36/1.53  #Partial instantiations: 0
% 2.36/1.53  #Strategies tried      : 1
% 2.36/1.53  
% 2.36/1.53  Timing (in seconds)
% 2.36/1.53  ----------------------
% 2.36/1.53  Preprocessing        : 0.27
% 2.36/1.53  Parsing              : 0.14
% 2.36/1.53  CNF conversion       : 0.02
% 2.36/1.53  Main loop            : 0.24
% 2.36/1.53  Inferencing          : 0.08
% 2.36/1.53  Reduction            : 0.07
% 2.36/1.53  Demodulation         : 0.05
% 2.36/1.53  BG Simplification    : 0.02
% 2.36/1.53  Subsumption          : 0.06
% 2.36/1.53  Abstraction          : 0.01
% 2.36/1.53  MUC search           : 0.00
% 2.36/1.53  Cooper               : 0.00
% 2.36/1.53  Total                : 0.54
% 2.36/1.54  Index Insertion      : 0.00
% 2.36/1.54  Index Deletion       : 0.00
% 2.36/1.54  Index Matching       : 0.00
% 2.36/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
