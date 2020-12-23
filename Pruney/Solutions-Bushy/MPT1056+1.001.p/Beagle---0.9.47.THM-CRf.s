%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1056+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:20 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 10.05s
% Verified   : 
% Statistics : Number of formulae       :  134 (1642 expanded)
%              Number of leaves         :   39 ( 593 expanded)
%              Depth                    :   25
%              Number of atoms          :  296 (8652 expanded)
%              Number of equality atoms :   46 (1300 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,D,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                       => ( ! [F] :
                              ( m1_subset_1(F,A)
                             => ( r2_hidden(F,D)
                               => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                         => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_29,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_38,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_74,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,B_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_86,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_74])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_225,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k2_partfun1(A_146,B_147,C_148,D_149) = k7_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_232,plain,(
    ! [D_149] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_6',D_149) = k7_relat_1('#skF_6',D_149)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_225])).

tff(c_239,plain,(
    ! [D_149] : k2_partfun1('#skF_5','#skF_3','#skF_6',D_149) = k7_relat_1('#skF_6',D_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_232])).

tff(c_598,plain,(
    ! [B_210,A_211,D_212,C_213] :
      ( k1_xboole_0 = B_210
      | v1_funct_2(k2_partfun1(A_211,B_210,D_212,C_213),C_213,B_210)
      | ~ r1_tarski(C_213,A_211)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_2(D_212,A_211,B_210)
      | ~ v1_funct_1(D_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_615,plain,(
    ! [C_213] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(k2_partfun1('#skF_5','#skF_3','#skF_6',C_213),C_213,'#skF_3')
      | ~ r1_tarski(C_213,'#skF_5')
      | ~ v1_funct_2('#skF_6','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_598])).

tff(c_635,plain,(
    ! [C_213] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(k7_relat_1('#skF_6',C_213),C_213,'#skF_3')
      | ~ r1_tarski(C_213,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_239,c_615])).

tff(c_661,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_4,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_664,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_69])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_664])).

tff(c_669,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_230,plain,(
    ! [D_149] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_4',D_149) = k7_relat_1('#skF_4',D_149)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_225])).

tff(c_236,plain,(
    ! [D_149] : k2_partfun1('#skF_2','#skF_3','#skF_4',D_149) = k7_relat_1('#skF_4',D_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_230])).

tff(c_733,plain,(
    ! [B_234,A_235,D_236,C_237] :
      ( k1_xboole_0 = B_234
      | m1_subset_1(k2_partfun1(A_235,B_234,D_236,C_237),k1_zfmisc_1(k2_zfmisc_1(C_237,B_234)))
      | ~ r1_tarski(C_237,A_235)
      | ~ m1_subset_1(D_236,k1_zfmisc_1(k2_zfmisc_1(A_235,B_234)))
      | ~ v1_funct_2(D_236,A_235,B_234)
      | ~ v1_funct_1(D_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_766,plain,(
    ! [D_149] :
      ( k1_xboole_0 = '#skF_3'
      | m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1(D_149,'#skF_3')))
      | ~ r1_tarski(D_149,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_733])).

tff(c_786,plain,(
    ! [D_149] :
      ( k1_xboole_0 = '#skF_3'
      | m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1(D_149,'#skF_3')))
      | ~ r1_tarski(D_149,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_766])).

tff(c_787,plain,(
    ! [D_149] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1(D_149,'#skF_3')))
      | ~ r1_tarski(D_149,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_669,c_786])).

tff(c_46,plain,(
    k2_partfun1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_241,plain,(
    k7_relat_1('#skF_4','#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_46])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_613,plain,(
    ! [C_213] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_4',C_213),C_213,'#skF_3')
      | ~ r1_tarski(C_213,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_598])).

tff(c_632,plain,(
    ! [C_213] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(k7_relat_1('#skF_4',C_213),C_213,'#skF_3')
      | ~ r1_tarski(C_213,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_236,c_613])).

tff(c_702,plain,(
    ! [C_213] :
      ( v1_funct_2(k7_relat_1('#skF_4',C_213),C_213,'#skF_3')
      | ~ r1_tarski(C_213,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_669,c_632])).

tff(c_185,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( v1_funct_1(k2_partfun1(A_132,B_133,C_134,D_135))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_190,plain,(
    ! [D_135] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_4',D_135))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_185])).

tff(c_196,plain,(
    ! [D_135] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_4',D_135)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_190])).

tff(c_240,plain,(
    ! [D_135] : v1_funct_1(k7_relat_1('#skF_4',D_135)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_196])).

tff(c_927,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( m1_subset_1('#skF_1'(A_246,B_247,C_248,D_249),A_246)
      | r2_relset_1(A_246,B_247,C_248,D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(D_249,A_246,B_247)
      | ~ v1_funct_1(D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(C_248,A_246,B_247)
      | ~ v1_funct_1(C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_952,plain,(
    ! [C_248] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_3',C_248,'#skF_6'),'#skF_5')
      | r2_relset_1('#skF_5','#skF_3',C_248,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_2(C_248,'#skF_5','#skF_3')
      | ~ v1_funct_1(C_248) ) ),
    inference(resolution,[status(thm)],[c_50,c_927])).

tff(c_1125,plain,(
    ! [C_268] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_3',C_268,'#skF_6'),'#skF_5')
      | r2_relset_1('#skF_5','#skF_3',C_268,'#skF_6')
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_2(C_268,'#skF_5','#skF_3')
      | ~ v1_funct_1(C_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_952])).

tff(c_1129,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k7_relat_1('#skF_4','#skF_5'),'#skF_5','#skF_3')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_787,c_1125])).

tff(c_1161,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k7_relat_1('#skF_4','#skF_5'),'#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_240,c_1129])).

tff(c_4088,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_5'),'#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1161])).

tff(c_4091,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_702,c_4088])).

tff(c_4095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4091])).

tff(c_4096,plain,
    ( r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')
    | m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1161])).

tff(c_4176,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4096])).

tff(c_24,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_101,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_101])).

tff(c_4097,plain,(
    v1_funct_2(k7_relat_1('#skF_4','#skF_5'),'#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1161])).

tff(c_126,plain,(
    ! [A_113,C_114,B_115] :
      ( m1_subset_1(A_113,C_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(C_114))
      | ~ r2_hidden(A_113,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_150,plain,(
    ! [A_119] :
      ( m1_subset_1(A_119,'#skF_2')
      | ~ r2_hidden(A_119,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_126])).

tff(c_154,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,'#skF_2')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_28,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_150])).

tff(c_157,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,'#skF_2')
      | ~ m1_subset_1(A_28,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_154])).

tff(c_4189,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4176,c_157])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k3_funct_2(A_12,B_13,C_14,D_15) = k1_funct_1(C_14,D_15)
      | ~ m1_subset_1(D_15,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4191,plain,(
    ! [B_13,C_14] :
      ( k3_funct_2('#skF_2',B_13,C_14,'#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1(C_14,'#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_13)))
      | ~ v1_funct_2(C_14,'#skF_2',B_13)
      | ~ v1_funct_1(C_14)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4189,c_14])).

tff(c_4542,plain,(
    ! [B_648,C_649] :
      ( k3_funct_2('#skF_2',B_648,C_649,'#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1(C_649,'#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'))
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_648)))
      | ~ v1_funct_2(C_649,'#skF_2',B_648)
      | ~ v1_funct_1(C_649) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4191])).

tff(c_4597,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1('#skF_4','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4542])).

tff(c_4634,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1('#skF_4','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4597])).

tff(c_93,plain,(
    ! [F_106] :
      ( k3_funct_2('#skF_2','#skF_3','#skF_4',F_106) = k1_funct_1('#skF_6',F_106)
      | ~ r2_hidden(F_106,'#skF_5')
      | ~ m1_subset_1(F_106,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_97,plain,(
    ! [A_28] :
      ( k3_funct_2('#skF_2','#skF_3','#skF_4',A_28) = k1_funct_1('#skF_6',A_28)
      | ~ m1_subset_1(A_28,'#skF_2')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_28,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_100,plain,(
    ! [A_28] :
      ( k3_funct_2('#skF_2','#skF_3','#skF_4',A_28) = k1_funct_1('#skF_6',A_28)
      | ~ m1_subset_1(A_28,'#skF_2')
      | ~ m1_subset_1(A_28,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_97])).

tff(c_4188,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4176,c_100])).

tff(c_7083,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1('#skF_4','#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4189,c_4634,c_4188])).

tff(c_44,plain,(
    ! [C_41,B_40,A_39] :
      ( k1_funct_1(k7_relat_1(C_41,B_40),A_39) = k1_funct_1(C_41,A_39)
      | ~ r2_hidden(A_39,B_40)
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1062,plain,(
    ! [D_257,A_258,B_259,C_260] :
      ( k1_funct_1(D_257,'#skF_1'(A_258,B_259,C_260,D_257)) != k1_funct_1(C_260,'#skF_1'(A_258,B_259,C_260,D_257))
      | r2_relset_1(A_258,B_259,C_260,D_257)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(D_257,A_258,B_259)
      | ~ v1_funct_1(D_257)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8838,plain,(
    ! [C_938,A_939,D_941,B_940,B_937] :
      ( k1_funct_1(D_941,'#skF_1'(A_939,B_940,k7_relat_1(C_938,B_937),D_941)) != k1_funct_1(C_938,'#skF_1'(A_939,B_940,k7_relat_1(C_938,B_937),D_941))
      | r2_relset_1(A_939,B_940,k7_relat_1(C_938,B_937),D_941)
      | ~ m1_subset_1(D_941,k1_zfmisc_1(k2_zfmisc_1(A_939,B_940)))
      | ~ v1_funct_2(D_941,A_939,B_940)
      | ~ v1_funct_1(D_941)
      | ~ m1_subset_1(k7_relat_1(C_938,B_937),k1_zfmisc_1(k2_zfmisc_1(A_939,B_940)))
      | ~ v1_funct_2(k7_relat_1(C_938,B_937),A_939,B_940)
      | ~ v1_funct_1(k7_relat_1(C_938,B_937))
      | ~ r2_hidden('#skF_1'(A_939,B_940,k7_relat_1(C_938,B_937),D_941),B_937)
      | ~ v1_funct_1(C_938)
      | ~ v1_relat_1(C_938) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1062])).

tff(c_8840,plain,
    ( r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2(k7_relat_1('#skF_4','#skF_5'),'#skF_5','#skF_3')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7083,c_8838])).

tff(c_8849,plain,
    ( r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_240,c_4097,c_54,c_52,c_50,c_8840])).

tff(c_8850,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8849])).

tff(c_8853,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_8850])).

tff(c_8856,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4176,c_8853])).

tff(c_8858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8856])).

tff(c_8859,plain,
    ( ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_8849])).

tff(c_9160,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_8859])).

tff(c_9163,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_787,c_9160])).

tff(c_9170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9163])).

tff(c_9171,plain,(
    r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_8859])).

tff(c_18,plain,(
    ! [D_19,C_18,A_16,B_17] :
      ( D_19 = C_18
      | ~ r2_relset_1(A_16,B_17,C_18,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9174,plain,
    ( k7_relat_1('#skF_4','#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_9171,c_18])).

tff(c_9177,plain,
    ( k7_relat_1('#skF_4','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9174])).

tff(c_9178,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_9177])).

tff(c_9181,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_787,c_9178])).

tff(c_9188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9181])).

tff(c_9189,plain,(
    r2_relset_1('#skF_5','#skF_3',k7_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4096])).

tff(c_9192,plain,
    ( k7_relat_1('#skF_4','#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_9189,c_18])).

tff(c_9195,plain,
    ( k7_relat_1('#skF_4','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9192])).

tff(c_9196,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_9195])).

tff(c_9199,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_787,c_9196])).

tff(c_9206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9199])).

%------------------------------------------------------------------------------
