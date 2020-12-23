%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 172 expanded)
%              Number of leaves         :   35 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 445 expanded)
%              Number of equality atoms :   36 ( 123 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_156,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_160,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_156])).

tff(c_44,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_161,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_44])).

tff(c_99,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_141,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_141])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_177,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_181,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_177])).

tff(c_328,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_xboole_0 = B_116
      | k1_relset_1(A_117,B_116,C_118) = A_117
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_331,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_328])).

tff(c_334,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_181,c_331])).

tff(c_335,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_54,plain,(
    ! [D_31] :
      ( r2_hidden('#skF_5'(D_31),'#skF_2')
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_116,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [D_31,B_54] :
      ( r2_hidden('#skF_5'(D_31),B_54)
      | ~ r1_tarski('#skF_2',B_54)
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_116])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_4','#skF_5'(D_31)) = D_31
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_204,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(k1_funct_1(B_81,A_82),k2_relat_1(B_81))
      | ~ r2_hidden(A_82,k1_relat_1(B_81))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_31),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_204])).

tff(c_213,plain,(
    ! [D_83] :
      ( r2_hidden(D_83,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_83),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_83,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50,c_209])).

tff(c_218,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_122,c_213])).

tff(c_219,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_336,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_219])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_336])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_127,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_138,plain,(
    ! [B_58] :
      ( k2_relat_1(B_58) = k1_xboole_0
      | ~ v5_relat_1(B_58,k1_xboole_0)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_127,c_85])).

tff(c_414,plain,(
    ! [B_124] :
      ( k2_relat_1(B_124) = '#skF_3'
      | ~ v5_relat_1(B_124,'#skF_3')
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_138])).

tff(c_417,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_414])).

tff(c_420,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_417])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_420])).

tff(c_433,plain,(
    ! [D_125] :
      ( r2_hidden(D_125,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_125,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_472,plain,(
    ! [A_133] :
      ( r1_tarski(A_133,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_133,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_433,c_4])).

tff(c_482,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_472])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(B_58) = A_59
      | ~ r1_tarski(A_59,k2_relat_1(B_58))
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_127,c_8])).

tff(c_485,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_482,c_139])).

tff(c_492,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_145,c_485])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:09 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.87/1.42  
% 2.87/1.42  %Foreground sorts:
% 2.87/1.42  
% 2.87/1.42  
% 2.87/1.42  %Background operators:
% 2.87/1.42  
% 2.87/1.42  
% 2.87/1.42  %Foreground operators:
% 2.87/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.42  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.87/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.87/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.87/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.42  
% 2.87/1.44  tff(f_109, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.87/1.44  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.87/1.44  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.87/1.44  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.87/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.87/1.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.87/1.44  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.44  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.87/1.44  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.87/1.44  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.87/1.44  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.44  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_156, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.44  tff(c_160, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_156])).
% 2.87/1.44  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_161, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_44])).
% 2.87/1.44  tff(c_99, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.87/1.44  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_99])).
% 2.87/1.44  tff(c_141, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.44  tff(c_145, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_141])).
% 2.87/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.44  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_177, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.87/1.44  tff(c_181, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_177])).
% 2.87/1.44  tff(c_328, plain, (![B_116, A_117, C_118]: (k1_xboole_0=B_116 | k1_relset_1(A_117, B_116, C_118)=A_117 | ~v1_funct_2(C_118, A_117, B_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.87/1.44  tff(c_331, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_328])).
% 2.87/1.44  tff(c_334, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_181, c_331])).
% 2.87/1.44  tff(c_335, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_334])).
% 2.87/1.44  tff(c_54, plain, (![D_31]: (r2_hidden('#skF_5'(D_31), '#skF_2') | ~r2_hidden(D_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_116, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_122, plain, (![D_31, B_54]: (r2_hidden('#skF_5'(D_31), B_54) | ~r1_tarski('#skF_2', B_54) | ~r2_hidden(D_31, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_116])).
% 2.87/1.44  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_52, plain, (![D_31]: (k1_funct_1('#skF_4', '#skF_5'(D_31))=D_31 | ~r2_hidden(D_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_204, plain, (![B_81, A_82]: (r2_hidden(k1_funct_1(B_81, A_82), k2_relat_1(B_81)) | ~r2_hidden(A_82, k1_relat_1(B_81)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.44  tff(c_209, plain, (![D_31]: (r2_hidden(D_31, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_31), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_31, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_204])).
% 2.87/1.44  tff(c_213, plain, (![D_83]: (r2_hidden(D_83, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_83), k1_relat_1('#skF_4')) | ~r2_hidden(D_83, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50, c_209])).
% 2.87/1.44  tff(c_218, plain, (![D_31]: (r2_hidden(D_31, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_31, '#skF_3'))), inference(resolution, [status(thm)], [c_122, c_213])).
% 2.87/1.44  tff(c_219, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_218])).
% 2.87/1.44  tff(c_336, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_219])).
% 2.87/1.44  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_336])).
% 2.87/1.44  tff(c_342, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_334])).
% 2.87/1.44  tff(c_127, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.44  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.44  tff(c_76, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.44  tff(c_85, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_76])).
% 2.87/1.44  tff(c_138, plain, (![B_58]: (k2_relat_1(B_58)=k1_xboole_0 | ~v5_relat_1(B_58, k1_xboole_0) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_127, c_85])).
% 2.87/1.44  tff(c_414, plain, (![B_124]: (k2_relat_1(B_124)='#skF_3' | ~v5_relat_1(B_124, '#skF_3') | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_138])).
% 2.87/1.44  tff(c_417, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_145, c_414])).
% 2.87/1.44  tff(c_420, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_417])).
% 2.87/1.44  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_420])).
% 2.87/1.44  tff(c_433, plain, (![D_125]: (r2_hidden(D_125, k2_relat_1('#skF_4')) | ~r2_hidden(D_125, '#skF_3'))), inference(splitRight, [status(thm)], [c_218])).
% 2.87/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_472, plain, (![A_133]: (r1_tarski(A_133, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_133, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_433, c_4])).
% 2.87/1.44  tff(c_482, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_472])).
% 2.87/1.44  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.44  tff(c_139, plain, (![B_58, A_59]: (k2_relat_1(B_58)=A_59 | ~r1_tarski(A_59, k2_relat_1(B_58)) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_127, c_8])).
% 2.87/1.44  tff(c_485, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_482, c_139])).
% 2.87/1.44  tff(c_492, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_145, c_485])).
% 2.87/1.44  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_492])).
% 2.87/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  Inference rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Ref     : 0
% 2.87/1.44  #Sup     : 85
% 2.87/1.44  #Fact    : 0
% 2.87/1.44  #Define  : 0
% 2.87/1.44  #Split   : 5
% 2.87/1.44  #Chain   : 0
% 2.87/1.44  #Close   : 0
% 2.87/1.44  
% 2.87/1.44  Ordering : KBO
% 2.87/1.44  
% 2.87/1.44  Simplification rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Subsume      : 12
% 2.87/1.44  #Demod        : 56
% 2.87/1.44  #Tautology    : 26
% 2.87/1.44  #SimpNegUnit  : 2
% 2.87/1.44  #BackRed      : 21
% 2.87/1.44  
% 2.87/1.44  #Partial instantiations: 0
% 2.87/1.44  #Strategies tried      : 1
% 2.87/1.44  
% 2.87/1.44  Timing (in seconds)
% 2.87/1.44  ----------------------
% 2.87/1.45  Preprocessing        : 0.34
% 2.87/1.45  Parsing              : 0.17
% 2.87/1.45  CNF conversion       : 0.02
% 2.87/1.45  Main loop            : 0.34
% 2.87/1.45  Inferencing          : 0.12
% 2.87/1.45  Reduction            : 0.10
% 2.87/1.45  Demodulation         : 0.07
% 2.87/1.45  BG Simplification    : 0.02
% 2.87/1.45  Subsumption          : 0.08
% 2.87/1.45  Abstraction          : 0.02
% 2.87/1.45  MUC search           : 0.00
% 2.87/1.45  Cooper               : 0.00
% 2.87/1.45  Total                : 0.72
% 2.87/1.45  Index Insertion      : 0.00
% 2.87/1.45  Index Deletion       : 0.00
% 2.87/1.45  Index Matching       : 0.00
% 2.87/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
