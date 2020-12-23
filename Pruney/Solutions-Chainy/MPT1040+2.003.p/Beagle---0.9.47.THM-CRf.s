%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 226 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 778 expanded)
%              Number of equality atoms :   13 ( 195 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_79,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_partfun1(C_57,A_58)
      | ~ v1_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_79])).

tff(c_88,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_82])).

tff(c_92,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_95,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_95])).

tff(c_100,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_204,plain,(
    ! [F_102,A_103,B_104,C_105] :
      ( r2_hidden(F_102,k5_partfun1(A_103,B_104,C_105))
      | ~ r1_partfun1(C_105,F_102)
      | ~ v1_partfun1(F_102,A_103)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_206,plain,(
    ! [C_105] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_105))
      | ~ r1_partfun1(C_105,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_54,c_204])).

tff(c_215,plain,(
    ! [C_106] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_106))
      | ~ r1_partfun1(C_106,'#skF_8')
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_100,c_206])).

tff(c_221,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_215])).

tff(c_227,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_221])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_227])).

tff(c_231,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_230,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_238,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_230])).

tff(c_259,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_48])).

tff(c_261,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_60])).

tff(c_262,plain,(
    ! [C_108,A_109,B_110] :
      ( v1_partfun1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_269,plain,
    ( v1_partfun1('#skF_7','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_261,c_262])).

tff(c_271,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_248,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_56])).

tff(c_260,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_54])).

tff(c_272,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_partfun1(C_111,A_112)
      | ~ v1_funct_2(C_111,A_112,B_113)
      | ~ v1_funct_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | v1_xboole_0(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_278,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_260,c_272])).

tff(c_285,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_248,c_278])).

tff(c_286,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_285])).

tff(c_445,plain,(
    ! [F_162,A_163,B_164,C_165] :
      ( r2_hidden(F_162,k5_partfun1(A_163,B_164,C_165))
      | ~ r1_partfun1(C_165,F_162)
      | ~ v1_partfun1(F_162,A_163)
      | ~ m1_subset_1(F_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(F_162)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_449,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_165))
      | ~ r1_partfun1(C_165,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_260,c_445])).

tff(c_456,plain,(
    ! [C_166] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_166))
      | ~ r1_partfun1(C_166,'#skF_8')
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_286,c_449])).

tff(c_459,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_261,c_456])).

tff(c_465,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_459])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_465])).

tff(c_469,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_270,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_260,c_262])).

tff(c_476,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_270])).

tff(c_590,plain,(
    ! [F_212,A_213,B_214,C_215] :
      ( r2_hidden(F_212,k5_partfun1(A_213,B_214,C_215))
      | ~ r1_partfun1(C_215,F_212)
      | ~ v1_partfun1(F_212,A_213)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_1(C_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_594,plain,(
    ! [C_215] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_215))
      | ~ r1_partfun1(C_215,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_260,c_590])).

tff(c_648,plain,(
    ! [C_221] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_221))
      | ~ r1_partfun1(C_221,'#skF_8')
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_476,c_594])).

tff(c_655,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_261,c_648])).

tff(c_662,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_655])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.54  
% 3.20/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.55  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.20/1.55  
% 3.20/1.55  %Foreground sorts:
% 3.20/1.55  
% 3.20/1.55  
% 3.20/1.55  %Background operators:
% 3.20/1.55  
% 3.20/1.55  
% 3.20/1.55  %Foreground operators:
% 3.20/1.55  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.20/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.20/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.20/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.55  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.20/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.20/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.20/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.20/1.55  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 3.20/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.55  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.20/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.55  
% 3.20/1.56  tff(f_93, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 3.20/1.56  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.20/1.56  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 3.20/1.56  tff(f_72, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 3.20/1.56  tff(f_37, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.20/1.56  tff(c_48, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_52, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_58, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_50, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_68, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_50])).
% 3.20/1.56  tff(c_56, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.56  tff(c_79, plain, (![C_57, A_58, B_59]: (v1_partfun1(C_57, A_58) | ~v1_funct_2(C_57, A_58, B_59) | ~v1_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.56  tff(c_82, plain, (v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_79])).
% 3.20/1.56  tff(c_88, plain, (v1_partfun1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_82])).
% 3.20/1.56  tff(c_92, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_88])).
% 3.20/1.56  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.20/1.56  tff(c_95, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_92, c_4])).
% 3.20/1.56  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_95])).
% 3.20/1.56  tff(c_100, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 3.20/1.56  tff(c_204, plain, (![F_102, A_103, B_104, C_105]: (r2_hidden(F_102, k5_partfun1(A_103, B_104, C_105)) | ~r1_partfun1(C_105, F_102) | ~v1_partfun1(F_102, A_103) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(F_102) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(C_105))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.56  tff(c_206, plain, (![C_105]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', C_105)) | ~r1_partfun1(C_105, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_105))), inference(resolution, [status(thm)], [c_54, c_204])).
% 3.20/1.56  tff(c_215, plain, (![C_106]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', C_106)) | ~r1_partfun1(C_106, '#skF_8') | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_106))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_100, c_206])).
% 3.20/1.56  tff(c_221, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_215])).
% 3.20/1.56  tff(c_227, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_221])).
% 3.20/1.56  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_227])).
% 3.20/1.56  tff(c_231, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 3.20/1.56  tff(c_230, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 3.20/1.56  tff(c_238, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_231, c_230])).
% 3.20/1.56  tff(c_259, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_48])).
% 3.20/1.56  tff(c_261, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_60])).
% 3.20/1.56  tff(c_262, plain, (![C_108, A_109, B_110]: (v1_partfun1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.56  tff(c_269, plain, (v1_partfun1('#skF_7', '#skF_6') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_261, c_262])).
% 3.20/1.56  tff(c_271, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_269])).
% 3.20/1.56  tff(c_248, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_56])).
% 3.20/1.56  tff(c_260, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_54])).
% 3.20/1.56  tff(c_272, plain, (![C_111, A_112, B_113]: (v1_partfun1(C_111, A_112) | ~v1_funct_2(C_111, A_112, B_113) | ~v1_funct_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | v1_xboole_0(B_113))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.56  tff(c_278, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_260, c_272])).
% 3.20/1.56  tff(c_285, plain, (v1_partfun1('#skF_8', '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_248, c_278])).
% 3.20/1.56  tff(c_286, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_271, c_285])).
% 3.20/1.56  tff(c_445, plain, (![F_162, A_163, B_164, C_165]: (r2_hidden(F_162, k5_partfun1(A_163, B_164, C_165)) | ~r1_partfun1(C_165, F_162) | ~v1_partfun1(F_162, A_163) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(F_162) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.56  tff(c_449, plain, (![C_165]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_165)) | ~r1_partfun1(C_165, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_165))), inference(resolution, [status(thm)], [c_260, c_445])).
% 3.20/1.56  tff(c_456, plain, (![C_166]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_166)) | ~r1_partfun1(C_166, '#skF_8') | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_166))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_286, c_449])).
% 3.20/1.56  tff(c_459, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_261, c_456])).
% 3.20/1.56  tff(c_465, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_459])).
% 3.20/1.56  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_465])).
% 3.20/1.56  tff(c_469, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_269])).
% 3.20/1.56  tff(c_270, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_260, c_262])).
% 3.20/1.56  tff(c_476, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_270])).
% 3.20/1.56  tff(c_590, plain, (![F_212, A_213, B_214, C_215]: (r2_hidden(F_212, k5_partfun1(A_213, B_214, C_215)) | ~r1_partfun1(C_215, F_212) | ~v1_partfun1(F_212, A_213) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_1(F_212) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_1(C_215))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.56  tff(c_594, plain, (![C_215]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_215)) | ~r1_partfun1(C_215, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_215))), inference(resolution, [status(thm)], [c_260, c_590])).
% 3.20/1.56  tff(c_648, plain, (![C_221]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_221)) | ~r1_partfun1(C_221, '#skF_8') | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_221))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_476, c_594])).
% 3.20/1.56  tff(c_655, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_261, c_648])).
% 3.20/1.56  tff(c_662, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_655])).
% 3.20/1.56  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_662])).
% 3.20/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.56  
% 3.20/1.56  Inference rules
% 3.20/1.56  ----------------------
% 3.20/1.56  #Ref     : 0
% 3.20/1.56  #Sup     : 114
% 3.20/1.56  #Fact    : 0
% 3.20/1.56  #Define  : 0
% 3.20/1.56  #Split   : 8
% 3.20/1.56  #Chain   : 0
% 3.20/1.56  #Close   : 0
% 3.20/1.56  
% 3.20/1.56  Ordering : KBO
% 3.20/1.56  
% 3.20/1.56  Simplification rules
% 3.20/1.56  ----------------------
% 3.20/1.56  #Subsume      : 4
% 3.20/1.56  #Demod        : 81
% 3.20/1.56  #Tautology    : 22
% 3.20/1.56  #SimpNegUnit  : 7
% 3.20/1.56  #BackRed      : 5
% 3.20/1.56  
% 3.20/1.56  #Partial instantiations: 0
% 3.20/1.56  #Strategies tried      : 1
% 3.20/1.56  
% 3.20/1.56  Timing (in seconds)
% 3.20/1.56  ----------------------
% 3.20/1.56  Preprocessing        : 0.38
% 3.20/1.56  Parsing              : 0.19
% 3.20/1.56  CNF conversion       : 0.03
% 3.20/1.56  Main loop            : 0.36
% 3.20/1.57  Inferencing          : 0.14
% 3.20/1.57  Reduction            : 0.11
% 3.20/1.57  Demodulation         : 0.08
% 3.20/1.57  BG Simplification    : 0.03
% 3.20/1.57  Subsumption          : 0.06
% 3.20/1.57  Abstraction          : 0.02
% 3.20/1.57  MUC search           : 0.00
% 3.20/1.57  Cooper               : 0.00
% 3.20/1.57  Total                : 0.78
% 3.20/1.57  Index Insertion      : 0.00
% 3.20/1.57  Index Deletion       : 0.00
% 3.20/1.57  Index Matching       : 0.00
% 3.20/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
