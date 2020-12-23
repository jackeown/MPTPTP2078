%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:10 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 116 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  136 ( 351 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_16,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_31,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_1'(A_33,B_34),A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_33] : r1_tarski(A_33,A_33) ),
    inference(resolution,[status(thm)],[c_31,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [C_39,B_40,A_41] :
      ( r2_hidden(C_39,B_40)
      | ~ r2_hidden(C_39,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_1,B_2,B_40] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_40)
      | ~ r1_tarski(A_1,B_40)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_24,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( r2_hidden('#skF_2'(A_46,B_47,C_48,D_49),A_46)
      | ~ r2_hidden(C_48,k2_relset_1(A_46,B_47,D_49))
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(D_49,A_46,B_47)
      | ~ v1_funct_1(D_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_74,plain,(
    ! [C_48] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_48,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_48,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_69])).

tff(c_92,plain,(
    ! [C_55] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_55,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_55,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_74])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [C_66,B_67] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_66,'#skF_6'),B_67)
      | ~ r1_tarski('#skF_4',B_67)
      | ~ r2_hidden(C_66,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_142,plain,(
    ! [C_68,B_69] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_68,'#skF_6'),B_69)
      | ~ r1_tarski('#skF_4',B_69)
      | ~ r2_hidden(C_68,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_129,c_8])).

tff(c_157,plain,(
    ! [A_1,B_2,B_69] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_1,B_2),'#skF_6'),B_69)
      | ~ r1_tarski('#skF_4',B_69)
      | ~ r1_tarski(A_1,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_54,c_142])).

tff(c_209,plain,(
    ! [D_85,A_86,B_87,C_88] :
      ( k1_funct_1(D_85,'#skF_2'(A_86,B_87,C_88,D_85)) = C_88
      | ~ r2_hidden(C_88,k2_relset_1(A_86,B_87,D_85))
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(D_85,A_86,B_87)
      | ~ v1_funct_1(D_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_225,plain,(
    ! [D_85,A_86,B_87,B_2] :
      ( k1_funct_1(D_85,'#skF_2'(A_86,B_87,'#skF_1'(k2_relset_1(A_86,B_87,D_85),B_2),D_85)) = '#skF_1'(k2_relset_1(A_86,B_87,D_85),B_2)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(D_85,A_86,B_87)
      | ~ v1_funct_1(D_85)
      | r1_tarski(k2_relset_1(A_86,B_87,D_85),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_105,plain,(
    ! [C_58] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_58,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_58,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_175,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_74,B_75),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_74,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_54,c_105])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k3_funct_2(A_8,B_9,C_10,D_11) = k1_funct_1(C_10,D_11)
      | ~ m1_subset_1(D_11,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_177,plain,(
    ! [B_9,C_10,A_74,B_75] :
      ( k3_funct_2('#skF_4',B_9,C_10,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_74,B_75),'#skF_6')) = k1_funct_1(C_10,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_74,B_75),'#skF_6'))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_9)))
      | ~ v1_funct_2(C_10,'#skF_4',B_9)
      | ~ v1_funct_1(C_10)
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(A_74,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_175,c_10])).

tff(c_227,plain,(
    ! [B_89,C_90,A_91,B_92] :
      ( k3_funct_2('#skF_4',B_89,C_90,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_91,B_92),'#skF_6')) = k1_funct_1(C_90,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_91,B_92),'#skF_6'))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_89)))
      | ~ v1_funct_2(C_90,'#skF_4',B_89)
      | ~ v1_funct_1(C_90)
      | ~ r1_tarski(A_91,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_91,B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_177])).

tff(c_244,plain,(
    ! [A_91,B_92] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_91,B_92),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_91,B_92),'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski(A_91,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_20,c_227])).

tff(c_396,plain,(
    ! [A_114,B_115] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_114,B_115),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_114,B_115),'#skF_6'))
      | ~ r1_tarski(A_114,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_114,B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_244])).

tff(c_18,plain,(
    ! [E_28] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_28),'#skF_3')
      | ~ m1_subset_1(E_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_501,plain,(
    ! [A_125,B_126] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_125,B_126),'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_125,B_126),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_125,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_125,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_18])).

tff(c_510,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_6'),'#skF_4')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_501])).

tff(c_544,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_129),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_129),'#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_39,c_510])).

tff(c_548,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(resolution,[status(thm)],[c_157,c_544])).

tff(c_570,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_130),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_39,c_548])).

tff(c_576,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_570,c_4])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:33:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.53  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.17/1.53  
% 3.17/1.53  %Foreground sorts:
% 3.17/1.53  
% 3.17/1.53  
% 3.17/1.53  %Background operators:
% 3.17/1.53  
% 3.17/1.53  
% 3.17/1.53  %Foreground operators:
% 3.17/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.17/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.17/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.17/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.53  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.17/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.53  
% 3.17/1.55  tff(f_86, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 3.17/1.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.17/1.55  tff(f_64, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 3.17/1.55  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.17/1.55  tff(f_49, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.17/1.55  tff(c_16, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.55  tff(c_31, plain, (![A_33, B_34]: (r2_hidden('#skF_1'(A_33, B_34), A_33) | r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.55  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.55  tff(c_39, plain, (![A_33]: (r1_tarski(A_33, A_33))), inference(resolution, [status(thm)], [c_31, c_4])).
% 3.17/1.55  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.55  tff(c_48, plain, (![C_39, B_40, A_41]: (r2_hidden(C_39, B_40) | ~r2_hidden(C_39, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.55  tff(c_54, plain, (![A_1, B_2, B_40]: (r2_hidden('#skF_1'(A_1, B_2), B_40) | ~r1_tarski(A_1, B_40) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_48])).
% 3.17/1.55  tff(c_24, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.55  tff(c_22, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.55  tff(c_20, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.55  tff(c_69, plain, (![A_46, B_47, C_48, D_49]: (r2_hidden('#skF_2'(A_46, B_47, C_48, D_49), A_46) | ~r2_hidden(C_48, k2_relset_1(A_46, B_47, D_49)) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(D_49, A_46, B_47) | ~v1_funct_1(D_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.17/1.55  tff(c_74, plain, (![C_48]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_48, '#skF_6'), '#skF_4') | ~r2_hidden(C_48, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_69])).
% 3.17/1.55  tff(c_92, plain, (![C_55]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_55, '#skF_6'), '#skF_4') | ~r2_hidden(C_55, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_74])).
% 3.17/1.55  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.55  tff(c_129, plain, (![C_66, B_67]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_66, '#skF_6'), B_67) | ~r1_tarski('#skF_4', B_67) | ~r2_hidden(C_66, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_92, c_2])).
% 3.17/1.55  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.55  tff(c_142, plain, (![C_68, B_69]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_68, '#skF_6'), B_69) | ~r1_tarski('#skF_4', B_69) | ~r2_hidden(C_68, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_129, c_8])).
% 3.17/1.55  tff(c_157, plain, (![A_1, B_2, B_69]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1, B_2), '#skF_6'), B_69) | ~r1_tarski('#skF_4', B_69) | ~r1_tarski(A_1, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_54, c_142])).
% 3.17/1.55  tff(c_209, plain, (![D_85, A_86, B_87, C_88]: (k1_funct_1(D_85, '#skF_2'(A_86, B_87, C_88, D_85))=C_88 | ~r2_hidden(C_88, k2_relset_1(A_86, B_87, D_85)) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(D_85, A_86, B_87) | ~v1_funct_1(D_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.17/1.55  tff(c_225, plain, (![D_85, A_86, B_87, B_2]: (k1_funct_1(D_85, '#skF_2'(A_86, B_87, '#skF_1'(k2_relset_1(A_86, B_87, D_85), B_2), D_85))='#skF_1'(k2_relset_1(A_86, B_87, D_85), B_2) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(D_85, A_86, B_87) | ~v1_funct_1(D_85) | r1_tarski(k2_relset_1(A_86, B_87, D_85), B_2))), inference(resolution, [status(thm)], [c_6, c_209])).
% 3.17/1.55  tff(c_28, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.55  tff(c_105, plain, (![C_58]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_58, '#skF_6'), '#skF_4') | ~r2_hidden(C_58, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_92, c_8])).
% 3.17/1.55  tff(c_175, plain, (![A_74, B_75]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_74, B_75), '#skF_6'), '#skF_4') | ~r1_tarski(A_74, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_54, c_105])).
% 3.17/1.55  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k3_funct_2(A_8, B_9, C_10, D_11)=k1_funct_1(C_10, D_11) | ~m1_subset_1(D_11, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_10, A_8, B_9) | ~v1_funct_1(C_10) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.55  tff(c_177, plain, (![B_9, C_10, A_74, B_75]: (k3_funct_2('#skF_4', B_9, C_10, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_74, B_75), '#skF_6'))=k1_funct_1(C_10, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_74, B_75), '#skF_6')) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_9))) | ~v1_funct_2(C_10, '#skF_4', B_9) | ~v1_funct_1(C_10) | v1_xboole_0('#skF_4') | ~r1_tarski(A_74, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_175, c_10])).
% 3.17/1.55  tff(c_227, plain, (![B_89, C_90, A_91, B_92]: (k3_funct_2('#skF_4', B_89, C_90, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_91, B_92), '#skF_6'))=k1_funct_1(C_90, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_91, B_92), '#skF_6')) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_89))) | ~v1_funct_2(C_90, '#skF_4', B_89) | ~v1_funct_1(C_90) | ~r1_tarski(A_91, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_91, B_92))), inference(negUnitSimplification, [status(thm)], [c_28, c_177])).
% 3.17/1.55  tff(c_244, plain, (![A_91, B_92]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_91, B_92), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_91, B_92), '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski(A_91, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_20, c_227])).
% 3.17/1.55  tff(c_396, plain, (![A_114, B_115]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_114, B_115), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_114, B_115), '#skF_6')) | ~r1_tarski(A_114, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_244])).
% 3.17/1.55  tff(c_18, plain, (![E_28]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_28), '#skF_3') | ~m1_subset_1(E_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.55  tff(c_501, plain, (![A_125, B_126]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_125, B_126), '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_125, B_126), '#skF_6'), '#skF_4') | ~r1_tarski(A_125, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_396, c_18])).
% 3.17/1.55  tff(c_510, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_6'), '#skF_4') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(superposition, [status(thm), theory('equality')], [c_225, c_501])).
% 3.17/1.55  tff(c_544, plain, (![B_129]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_129), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_129), '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_129))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_39, c_510])).
% 3.17/1.55  tff(c_548, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(resolution, [status(thm)], [c_157, c_544])).
% 3.17/1.55  tff(c_570, plain, (![B_130]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_130), '#skF_3') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_130))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_39, c_548])).
% 3.17/1.55  tff(c_576, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_570, c_4])).
% 3.17/1.55  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_576])).
% 3.17/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.55  
% 3.17/1.55  Inference rules
% 3.17/1.55  ----------------------
% 3.17/1.55  #Ref     : 0
% 3.17/1.55  #Sup     : 121
% 3.17/1.55  #Fact    : 0
% 3.17/1.55  #Define  : 0
% 3.17/1.55  #Split   : 3
% 3.17/1.55  #Chain   : 0
% 3.17/1.55  #Close   : 0
% 3.17/1.55  
% 3.17/1.55  Ordering : KBO
% 3.17/1.55  
% 3.17/1.55  Simplification rules
% 3.17/1.55  ----------------------
% 3.17/1.55  #Subsume      : 17
% 3.17/1.55  #Demod        : 52
% 3.17/1.55  #Tautology    : 15
% 3.17/1.55  #SimpNegUnit  : 4
% 3.17/1.55  #BackRed      : 0
% 3.17/1.55  
% 3.17/1.55  #Partial instantiations: 0
% 3.17/1.55  #Strategies tried      : 1
% 3.17/1.55  
% 3.17/1.55  Timing (in seconds)
% 3.17/1.55  ----------------------
% 3.17/1.55  Preprocessing        : 0.33
% 3.17/1.55  Parsing              : 0.18
% 3.17/1.55  CNF conversion       : 0.02
% 3.17/1.55  Main loop            : 0.39
% 3.17/1.55  Inferencing          : 0.16
% 3.17/1.55  Reduction            : 0.11
% 3.17/1.55  Demodulation         : 0.07
% 3.17/1.55  BG Simplification    : 0.02
% 3.17/1.55  Subsumption          : 0.08
% 3.17/1.55  Abstraction          : 0.03
% 3.17/1.55  MUC search           : 0.00
% 3.17/1.55  Cooper               : 0.00
% 3.17/1.55  Total                : 0.76
% 3.17/1.55  Index Insertion      : 0.00
% 3.17/1.55  Index Deletion       : 0.00
% 3.17/1.55  Index Matching       : 0.00
% 3.17/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
