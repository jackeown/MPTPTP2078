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
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   58 (  85 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 168 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    ! [A_29] :
      ( v1_relat_1(A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_62,plain,(
    ! [A_28] :
      ( v1_funct_1(A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_140,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_2'(A_57,B_58),k1_relat_1(B_58))
      | v5_funct_1(B_58,A_57)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_147,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_2'(A_57,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_57)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_140])).

tff(c_151,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_2'(A_57,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_66,c_147])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,B_43)
      | ~ r2_hidden(C_44,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | k4_xboole_0(A_47,B_46) != A_47 ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_113,plain,(
    ! [A_51,B_52,A_53] :
      ( ~ r2_hidden('#skF_1'(A_51,B_52),A_53)
      | k4_xboole_0(A_53,B_52) != A_53
      | r1_xboole_0(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_127,plain,(
    ! [B_54,A_55] :
      ( k4_xboole_0(B_54,B_54) != B_54
      | r1_xboole_0(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_132,plain,(
    ! [A_56] : r1_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_127])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_139,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_224,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_2'(A_67,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_66,c_147])).

tff(c_92,plain,(
    ! [C_44,B_8,A_7] :
      ( ~ r2_hidden(C_44,B_8)
      | ~ r2_hidden(C_44,A_7)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_230,plain,(
    ! [A_67,A_7] :
      ( ~ r2_hidden('#skF_2'(A_67,k1_xboole_0),A_7)
      | k4_xboole_0(A_7,k1_xboole_0) != A_7
      | v5_funct_1(k1_xboole_0,A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_224,c_92])).

tff(c_313,plain,(
    ! [A_83,A_84] :
      ( ~ r2_hidden('#skF_2'(A_83,k1_xboole_0),A_84)
      | v5_funct_1(k1_xboole_0,A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_230])).

tff(c_330,plain,(
    ! [A_85] :
      ( v5_funct_1(k1_xboole_0,A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_151,c_313])).

tff(c_38,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_333,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_330,c_38])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:39:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.18/1.25  
% 2.18/1.25  %Foreground sorts:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Background operators:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Foreground operators:
% 2.18/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.25  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.18/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.18/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.25  
% 2.18/1.26  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.18/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.18/1.26  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.18/1.26  tff(f_74, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.18/1.26  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.18/1.26  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.18/1.26  tff(f_46, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.18/1.26  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.18/1.26  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.18/1.26  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.26  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.18/1.26  tff(c_67, plain, (![A_29]: (v1_relat_1(A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.26  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_67])).
% 2.18/1.26  tff(c_62, plain, (![A_28]: (v1_funct_1(A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.26  tff(c_66, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_62])).
% 2.18/1.26  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.26  tff(c_140, plain, (![A_57, B_58]: (r2_hidden('#skF_2'(A_57, B_58), k1_relat_1(B_58)) | v5_funct_1(B_58, A_57) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.26  tff(c_147, plain, (![A_57]: (r2_hidden('#skF_2'(A_57, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_57) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_28, c_140])).
% 2.18/1.26  tff(c_151, plain, (![A_57]: (r2_hidden('#skF_2'(A_57, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_66, c_147])).
% 2.18/1.26  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.26  tff(c_14, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.26  tff(c_89, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, B_43) | ~r2_hidden(C_44, A_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.26  tff(c_93, plain, (![C_45, B_46, A_47]: (~r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | k4_xboole_0(A_47, B_46)!=A_47)), inference(resolution, [status(thm)], [c_14, c_89])).
% 2.18/1.26  tff(c_113, plain, (![A_51, B_52, A_53]: (~r2_hidden('#skF_1'(A_51, B_52), A_53) | k4_xboole_0(A_53, B_52)!=A_53 | r1_xboole_0(A_51, B_52))), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.18/1.26  tff(c_127, plain, (![B_54, A_55]: (k4_xboole_0(B_54, B_54)!=B_54 | r1_xboole_0(A_55, B_54))), inference(resolution, [status(thm)], [c_6, c_113])).
% 2.18/1.26  tff(c_132, plain, (![A_56]: (r1_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_127])).
% 2.18/1.26  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.26  tff(c_139, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=A_56)), inference(resolution, [status(thm)], [c_132, c_12])).
% 2.18/1.26  tff(c_224, plain, (![A_67]: (r2_hidden('#skF_2'(A_67, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_66, c_147])).
% 2.18/1.26  tff(c_92, plain, (![C_44, B_8, A_7]: (~r2_hidden(C_44, B_8) | ~r2_hidden(C_44, A_7) | k4_xboole_0(A_7, B_8)!=A_7)), inference(resolution, [status(thm)], [c_14, c_89])).
% 2.18/1.26  tff(c_230, plain, (![A_67, A_7]: (~r2_hidden('#skF_2'(A_67, k1_xboole_0), A_7) | k4_xboole_0(A_7, k1_xboole_0)!=A_7 | v5_funct_1(k1_xboole_0, A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_224, c_92])).
% 2.18/1.26  tff(c_313, plain, (![A_83, A_84]: (~r2_hidden('#skF_2'(A_83, k1_xboole_0), A_84) | v5_funct_1(k1_xboole_0, A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_230])).
% 2.18/1.26  tff(c_330, plain, (![A_85]: (v5_funct_1(k1_xboole_0, A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_151, c_313])).
% 2.18/1.26  tff(c_38, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.26  tff(c_333, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_330, c_38])).
% 2.18/1.26  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_333])).
% 2.18/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  Inference rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Ref     : 0
% 2.18/1.26  #Sup     : 66
% 2.18/1.26  #Fact    : 0
% 2.18/1.26  #Define  : 0
% 2.18/1.26  #Split   : 0
% 2.18/1.26  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 4
% 2.18/1.26  #Demod        : 21
% 2.18/1.26  #Tautology    : 25
% 2.18/1.26  #SimpNegUnit  : 0
% 2.18/1.26  #BackRed      : 0
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.36/1.27  Preprocessing        : 0.28
% 2.36/1.27  Parsing              : 0.16
% 2.36/1.27  CNF conversion       : 0.02
% 2.36/1.27  Main loop            : 0.23
% 2.36/1.27  Inferencing          : 0.10
% 2.36/1.27  Reduction            : 0.06
% 2.36/1.27  Demodulation         : 0.04
% 2.36/1.27  BG Simplification    : 0.01
% 2.36/1.27  Subsumption          : 0.04
% 2.36/1.27  Abstraction          : 0.01
% 2.36/1.27  MUC search           : 0.00
% 2.36/1.27  Cooper               : 0.00
% 2.36/1.27  Total                : 0.54
% 2.36/1.27  Index Insertion      : 0.00
% 2.36/1.27  Index Deletion       : 0.00
% 2.36/1.27  Index Matching       : 0.00
% 2.36/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
