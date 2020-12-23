%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:40 EST 2020

% Result     : Theorem 9.92s
% Output     : CNFRefutation 10.26s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 194 expanded)
%              Number of leaves         :   38 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  208 ( 743 expanded)
%              Number of equality atoms :   48 ( 239 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_17 > #skF_6 > #skF_15 > #skF_2 > #skF_4 > #skF_16 > #skF_14 > #skF_5 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_13 > #skF_3 > #skF_12 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_68,plain,(
    k6_relat_1('#skF_15') != '#skF_17' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_82,plain,(
    v1_relat_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_80,plain,(
    v1_funct_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76,plain,(
    k1_relat_1('#skF_17') = '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6483,plain,(
    ! [B_544] :
      ( k1_funct_1(B_544,'#skF_14'(k1_relat_1(B_544),B_544)) != '#skF_14'(k1_relat_1(B_544),B_544)
      | k6_relat_1(k1_relat_1(B_544)) = B_544
      | ~ v1_funct_1(B_544)
      | ~ v1_relat_1(B_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6486,plain,
    ( k1_funct_1('#skF_17','#skF_14'('#skF_15','#skF_17')) != '#skF_14'(k1_relat_1('#skF_17'),'#skF_17')
    | k6_relat_1(k1_relat_1('#skF_17')) = '#skF_17'
    | ~ v1_funct_1('#skF_17')
    | ~ v1_relat_1('#skF_17') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6483])).

tff(c_6491,plain,
    ( k1_funct_1('#skF_17','#skF_14'('#skF_15','#skF_17')) != '#skF_14'('#skF_15','#skF_17')
    | k6_relat_1('#skF_15') = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_76,c_6486])).

tff(c_6492,plain,(
    k1_funct_1('#skF_17','#skF_14'('#skF_15','#skF_17')) != '#skF_14'('#skF_15','#skF_17') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6491])).

tff(c_100,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_1'(A_163,B_164),A_163)
      | r1_tarski(A_163,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_163] : r1_tarski(A_163,A_163) ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_217,plain,(
    ! [B_200] :
      ( r2_hidden('#skF_14'(k1_relat_1(B_200),B_200),k1_relat_1(B_200))
      | k6_relat_1(k1_relat_1(B_200)) = B_200
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_222,plain,
    ( r2_hidden('#skF_14'('#skF_15','#skF_17'),k1_relat_1('#skF_17'))
    | k6_relat_1(k1_relat_1('#skF_17')) = '#skF_17'
    | ~ v1_funct_1('#skF_17')
    | ~ v1_relat_1('#skF_17') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_217])).

tff(c_234,plain,
    ( r2_hidden('#skF_14'('#skF_15','#skF_17'),'#skF_15')
    | k6_relat_1('#skF_15') = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_76,c_222])).

tff(c_235,plain,(
    r2_hidden('#skF_14'('#skF_15','#skF_17'),'#skF_15') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_234])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_245,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_14'('#skF_15','#skF_17'),B_2)
      | ~ r1_tarski('#skF_15',B_2) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_74,plain,(
    r1_tarski(k2_relat_1('#skF_17'),'#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_153,plain,(
    ! [A_182,D_183] :
      ( r2_hidden(k1_funct_1(A_182,D_183),k2_relat_1(A_182))
      | ~ r2_hidden(D_183,k1_relat_1(A_182))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6390,plain,(
    ! [A_519,D_520,B_521] :
      ( r2_hidden(k1_funct_1(A_519,D_520),B_521)
      | ~ r1_tarski(k2_relat_1(A_519),B_521)
      | ~ r2_hidden(D_520,k1_relat_1(A_519))
      | ~ v1_funct_1(A_519)
      | ~ v1_relat_1(A_519) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_6596,plain,(
    ! [A_573,D_574,B_575,B_576] :
      ( r2_hidden(k1_funct_1(A_573,D_574),B_575)
      | ~ r1_tarski(B_576,B_575)
      | ~ r1_tarski(k2_relat_1(A_573),B_576)
      | ~ r2_hidden(D_574,k1_relat_1(A_573))
      | ~ v1_funct_1(A_573)
      | ~ v1_relat_1(A_573) ) ),
    inference(resolution,[status(thm)],[c_6390,c_2])).

tff(c_6603,plain,(
    ! [A_577,D_578] :
      ( r2_hidden(k1_funct_1(A_577,D_578),'#skF_15')
      | ~ r1_tarski(k2_relat_1(A_577),k2_relat_1('#skF_17'))
      | ~ r2_hidden(D_578,k1_relat_1(A_577))
      | ~ v1_funct_1(A_577)
      | ~ v1_relat_1(A_577) ) ),
    inference(resolution,[status(thm)],[c_74,c_6596])).

tff(c_6606,plain,(
    ! [D_578] :
      ( r2_hidden(k1_funct_1('#skF_17',D_578),'#skF_15')
      | ~ r2_hidden(D_578,k1_relat_1('#skF_17'))
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1('#skF_17') ) ),
    inference(resolution,[status(thm)],[c_105,c_6603])).

tff(c_6610,plain,(
    ! [D_579] :
      ( r2_hidden(k1_funct_1('#skF_17',D_579),'#skF_15')
      | ~ r2_hidden(D_579,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_6606])).

tff(c_6623,plain,(
    ! [D_579,B_2] :
      ( r2_hidden(k1_funct_1('#skF_17',D_579),B_2)
      | ~ r1_tarski('#skF_15',B_2)
      | ~ r2_hidden(D_579,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_6610,c_2])).

tff(c_86,plain,(
    v1_relat_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_84,plain,(
    v1_funct_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_72,plain,(
    v2_funct_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_78,plain,(
    k1_relat_1('#skF_16') = '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_62,plain,(
    ! [A_157,C_159] :
      ( r2_hidden(k4_tarski(A_157,k1_funct_1(C_159,A_157)),C_159)
      | ~ r2_hidden(A_157,k1_relat_1(C_159))
      | ~ v1_funct_1(C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    k5_relat_1('#skF_17','#skF_16') = '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_7394,plain,(
    ! [D_639,B_640,A_641,E_642] :
      ( r2_hidden(k4_tarski(D_639,'#skF_2'(B_640,k5_relat_1(A_641,B_640),D_639,A_641,E_642)),A_641)
      | ~ r2_hidden(k4_tarski(D_639,E_642),k5_relat_1(A_641,B_640))
      | ~ v1_relat_1(k5_relat_1(A_641,B_640))
      | ~ v1_relat_1(B_640)
      | ~ v1_relat_1(A_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7411,plain,(
    ! [D_639,E_642] :
      ( r2_hidden(k4_tarski(D_639,'#skF_2'('#skF_16','#skF_16',D_639,'#skF_17',E_642)),'#skF_17')
      | ~ r2_hidden(k4_tarski(D_639,E_642),k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_7394])).

tff(c_7419,plain,(
    ! [D_643,E_644] :
      ( r2_hidden(k4_tarski(D_643,'#skF_2'('#skF_16','#skF_16',D_643,'#skF_17',E_644)),'#skF_17')
      | ~ r2_hidden(k4_tarski(D_643,E_644),'#skF_16') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_86,c_70,c_70,c_7411])).

tff(c_64,plain,(
    ! [C_159,A_157,B_158] :
      ( k1_funct_1(C_159,A_157) = B_158
      | ~ r2_hidden(k4_tarski(A_157,B_158),C_159)
      | ~ v1_funct_1(C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7427,plain,(
    ! [D_643,E_644] :
      ( k1_funct_1('#skF_17',D_643) = '#skF_2'('#skF_16','#skF_16',D_643,'#skF_17',E_644)
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(k4_tarski(D_643,E_644),'#skF_16') ) ),
    inference(resolution,[status(thm)],[c_7419,c_64])).

tff(c_7460,plain,(
    ! [D_647,E_648] :
      ( k1_funct_1('#skF_17',D_647) = '#skF_2'('#skF_16','#skF_16',D_647,'#skF_17',E_648)
      | ~ r2_hidden(k4_tarski(D_647,E_648),'#skF_16') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_7427])).

tff(c_7472,plain,(
    ! [A_157] :
      ( '#skF_2'('#skF_16','#skF_16',A_157,'#skF_17',k1_funct_1('#skF_16',A_157)) = k1_funct_1('#skF_17',A_157)
      | ~ r2_hidden(A_157,k1_relat_1('#skF_16'))
      | ~ v1_funct_1('#skF_16')
      | ~ v1_relat_1('#skF_16') ) ),
    inference(resolution,[status(thm)],[c_62,c_7460])).

tff(c_7479,plain,(
    ! [A_157] :
      ( '#skF_2'('#skF_16','#skF_16',A_157,'#skF_17',k1_funct_1('#skF_16',A_157)) = k1_funct_1('#skF_17',A_157)
      | ~ r2_hidden(A_157,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_78,c_7472])).

tff(c_7690,plain,(
    ! [B_658,A_659,D_660,E_661] :
      ( r2_hidden(k4_tarski('#skF_2'(B_658,k5_relat_1(A_659,B_658),D_660,A_659,E_661),E_661),B_658)
      | ~ r2_hidden(k4_tarski(D_660,E_661),k5_relat_1(A_659,B_658))
      | ~ v1_relat_1(k5_relat_1(A_659,B_658))
      | ~ v1_relat_1(B_658)
      | ~ v1_relat_1(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7719,plain,(
    ! [D_660,E_661] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_16','#skF_16',D_660,'#skF_17',E_661),E_661),'#skF_16')
      | ~ r2_hidden(k4_tarski(D_660,E_661),k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_7690])).

tff(c_7734,plain,(
    ! [D_662,E_663] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_16','#skF_16',D_662,'#skF_17',E_663),E_663),'#skF_16')
      | ~ r2_hidden(k4_tarski(D_662,E_663),'#skF_16') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_86,c_70,c_70,c_7719])).

tff(c_7748,plain,(
    ! [D_662,E_663] :
      ( k1_funct_1('#skF_16','#skF_2'('#skF_16','#skF_16',D_662,'#skF_17',E_663)) = E_663
      | ~ v1_funct_1('#skF_16')
      | ~ v1_relat_1('#skF_16')
      | ~ r2_hidden(k4_tarski(D_662,E_663),'#skF_16') ) ),
    inference(resolution,[status(thm)],[c_7734,c_64])).

tff(c_7822,plain,(
    ! [D_668,E_669] :
      ( k1_funct_1('#skF_16','#skF_2'('#skF_16','#skF_16',D_668,'#skF_17',E_669)) = E_669
      | ~ r2_hidden(k4_tarski(D_668,E_669),'#skF_16') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_7748])).

tff(c_7841,plain,(
    ! [A_157] :
      ( k1_funct_1('#skF_16','#skF_2'('#skF_16','#skF_16',A_157,'#skF_17',k1_funct_1('#skF_16',A_157))) = k1_funct_1('#skF_16',A_157)
      | ~ r2_hidden(A_157,k1_relat_1('#skF_16'))
      | ~ v1_funct_1('#skF_16')
      | ~ v1_relat_1('#skF_16') ) ),
    inference(resolution,[status(thm)],[c_62,c_7822])).

tff(c_7874,plain,(
    ! [A_673] :
      ( k1_funct_1('#skF_16','#skF_2'('#skF_16','#skF_16',A_673,'#skF_17',k1_funct_1('#skF_16',A_673))) = k1_funct_1('#skF_16',A_673)
      | ~ r2_hidden(A_673,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_78,c_7841])).

tff(c_7954,plain,(
    ! [A_674] :
      ( k1_funct_1('#skF_16',k1_funct_1('#skF_17',A_674)) = k1_funct_1('#skF_16',A_674)
      | ~ r2_hidden(A_674,'#skF_15')
      | ~ r2_hidden(A_674,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7479,c_7874])).

tff(c_44,plain,(
    ! [C_151,B_150,A_145] :
      ( C_151 = B_150
      | k1_funct_1(A_145,C_151) != k1_funct_1(A_145,B_150)
      | ~ r2_hidden(C_151,k1_relat_1(A_145))
      | ~ r2_hidden(B_150,k1_relat_1(A_145))
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7980,plain,(
    ! [A_674,C_151] :
      ( k1_funct_1('#skF_17',A_674) = C_151
      | k1_funct_1('#skF_16',C_151) != k1_funct_1('#skF_16',A_674)
      | ~ r2_hidden(C_151,k1_relat_1('#skF_16'))
      | ~ r2_hidden(k1_funct_1('#skF_17',A_674),k1_relat_1('#skF_16'))
      | ~ v2_funct_1('#skF_16')
      | ~ v1_funct_1('#skF_16')
      | ~ v1_relat_1('#skF_16')
      | ~ r2_hidden(A_674,'#skF_15')
      | ~ r2_hidden(A_674,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7954,c_44])).

tff(c_8017,plain,(
    ! [A_674,C_151] :
      ( k1_funct_1('#skF_17',A_674) = C_151
      | k1_funct_1('#skF_16',C_151) != k1_funct_1('#skF_16',A_674)
      | ~ r2_hidden(C_151,'#skF_15')
      | ~ r2_hidden(k1_funct_1('#skF_17',A_674),'#skF_15')
      | ~ r2_hidden(A_674,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_72,c_78,c_78,c_7980])).

tff(c_17030,plain,(
    ! [A_1068] :
      ( k1_funct_1('#skF_17',A_1068) = A_1068
      | ~ r2_hidden(A_1068,'#skF_15')
      | ~ r2_hidden(k1_funct_1('#skF_17',A_1068),'#skF_15')
      | ~ r2_hidden(A_1068,'#skF_15') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8017])).

tff(c_17047,plain,(
    ! [D_579] :
      ( k1_funct_1('#skF_17',D_579) = D_579
      | ~ r1_tarski('#skF_15','#skF_15')
      | ~ r2_hidden(D_579,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_6623,c_17030])).

tff(c_17082,plain,(
    ! [D_1069] :
      ( k1_funct_1('#skF_17',D_1069) = D_1069
      | ~ r2_hidden(D_1069,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_17047])).

tff(c_17408,plain,
    ( k1_funct_1('#skF_17','#skF_14'('#skF_15','#skF_17')) = '#skF_14'('#skF_15','#skF_17')
    | ~ r1_tarski('#skF_15','#skF_15') ),
    inference(resolution,[status(thm)],[c_245,c_17082])).

tff(c_17567,plain,(
    k1_funct_1('#skF_17','#skF_14'('#skF_15','#skF_17')) = '#skF_14'('#skF_15','#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_17408])).

tff(c_17569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6492,c_17567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.92/3.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.92/3.99  
% 9.92/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.92/4.00  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_17 > #skF_6 > #skF_15 > #skF_2 > #skF_4 > #skF_16 > #skF_14 > #skF_5 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_13 > #skF_3 > #skF_12 > #skF_1 > #skF_9
% 9.92/4.00  
% 9.92/4.00  %Foreground sorts:
% 9.92/4.00  
% 9.92/4.00  
% 9.92/4.00  %Background operators:
% 9.92/4.00  
% 9.92/4.00  
% 9.92/4.00  %Foreground operators:
% 9.92/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.92/4.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.92/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.92/4.00  tff('#skF_17', type, '#skF_17': $i).
% 9.92/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.92/4.00  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.92/4.00  tff('#skF_15', type, '#skF_15': $i).
% 9.92/4.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 9.92/4.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.92/4.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.92/4.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.92/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.92/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.92/4.00  tff('#skF_16', type, '#skF_16': $i).
% 9.92/4.00  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 9.92/4.00  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.92/4.00  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 9.92/4.00  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 9.92/4.00  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 9.92/4.00  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.92/4.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.92/4.00  tff('#skF_13', type, '#skF_13': $i > $i).
% 9.92/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.92/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.92/4.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.92/4.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.92/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.92/4.00  tff('#skF_12', type, '#skF_12': $i > $i).
% 9.92/4.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.92/4.00  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.92/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.92/4.00  
% 10.26/4.01  tff(f_125, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 10.26/4.01  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 10.26/4.01  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.26/4.01  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 10.26/4.01  tff(f_103, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.26/4.01  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 10.26/4.01  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 10.26/4.01  tff(c_68, plain, (k6_relat_1('#skF_15')!='#skF_17'), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_82, plain, (v1_relat_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_80, plain, (v1_funct_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_76, plain, (k1_relat_1('#skF_17')='#skF_15'), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_6483, plain, (![B_544]: (k1_funct_1(B_544, '#skF_14'(k1_relat_1(B_544), B_544))!='#skF_14'(k1_relat_1(B_544), B_544) | k6_relat_1(k1_relat_1(B_544))=B_544 | ~v1_funct_1(B_544) | ~v1_relat_1(B_544))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.26/4.01  tff(c_6486, plain, (k1_funct_1('#skF_17', '#skF_14'('#skF_15', '#skF_17'))!='#skF_14'(k1_relat_1('#skF_17'), '#skF_17') | k6_relat_1(k1_relat_1('#skF_17'))='#skF_17' | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_76, c_6483])).
% 10.26/4.01  tff(c_6491, plain, (k1_funct_1('#skF_17', '#skF_14'('#skF_15', '#skF_17'))!='#skF_14'('#skF_15', '#skF_17') | k6_relat_1('#skF_15')='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_76, c_6486])).
% 10.26/4.01  tff(c_6492, plain, (k1_funct_1('#skF_17', '#skF_14'('#skF_15', '#skF_17'))!='#skF_14'('#skF_15', '#skF_17')), inference(negUnitSimplification, [status(thm)], [c_68, c_6491])).
% 10.26/4.01  tff(c_100, plain, (![A_163, B_164]: (r2_hidden('#skF_1'(A_163, B_164), A_163) | r1_tarski(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/4.01  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/4.01  tff(c_105, plain, (![A_163]: (r1_tarski(A_163, A_163))), inference(resolution, [status(thm)], [c_100, c_4])).
% 10.26/4.01  tff(c_217, plain, (![B_200]: (r2_hidden('#skF_14'(k1_relat_1(B_200), B_200), k1_relat_1(B_200)) | k6_relat_1(k1_relat_1(B_200))=B_200 | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.26/4.01  tff(c_222, plain, (r2_hidden('#skF_14'('#skF_15', '#skF_17'), k1_relat_1('#skF_17')) | k6_relat_1(k1_relat_1('#skF_17'))='#skF_17' | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_76, c_217])).
% 10.26/4.01  tff(c_234, plain, (r2_hidden('#skF_14'('#skF_15', '#skF_17'), '#skF_15') | k6_relat_1('#skF_15')='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_76, c_222])).
% 10.26/4.01  tff(c_235, plain, (r2_hidden('#skF_14'('#skF_15', '#skF_17'), '#skF_15')), inference(negUnitSimplification, [status(thm)], [c_68, c_234])).
% 10.26/4.01  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/4.01  tff(c_245, plain, (![B_2]: (r2_hidden('#skF_14'('#skF_15', '#skF_17'), B_2) | ~r1_tarski('#skF_15', B_2))), inference(resolution, [status(thm)], [c_235, c_2])).
% 10.26/4.01  tff(c_74, plain, (r1_tarski(k2_relat_1('#skF_17'), '#skF_15')), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_153, plain, (![A_182, D_183]: (r2_hidden(k1_funct_1(A_182, D_183), k2_relat_1(A_182)) | ~r2_hidden(D_183, k1_relat_1(A_182)) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.26/4.01  tff(c_6390, plain, (![A_519, D_520, B_521]: (r2_hidden(k1_funct_1(A_519, D_520), B_521) | ~r1_tarski(k2_relat_1(A_519), B_521) | ~r2_hidden(D_520, k1_relat_1(A_519)) | ~v1_funct_1(A_519) | ~v1_relat_1(A_519))), inference(resolution, [status(thm)], [c_153, c_2])).
% 10.26/4.01  tff(c_6596, plain, (![A_573, D_574, B_575, B_576]: (r2_hidden(k1_funct_1(A_573, D_574), B_575) | ~r1_tarski(B_576, B_575) | ~r1_tarski(k2_relat_1(A_573), B_576) | ~r2_hidden(D_574, k1_relat_1(A_573)) | ~v1_funct_1(A_573) | ~v1_relat_1(A_573))), inference(resolution, [status(thm)], [c_6390, c_2])).
% 10.26/4.01  tff(c_6603, plain, (![A_577, D_578]: (r2_hidden(k1_funct_1(A_577, D_578), '#skF_15') | ~r1_tarski(k2_relat_1(A_577), k2_relat_1('#skF_17')) | ~r2_hidden(D_578, k1_relat_1(A_577)) | ~v1_funct_1(A_577) | ~v1_relat_1(A_577))), inference(resolution, [status(thm)], [c_74, c_6596])).
% 10.26/4.01  tff(c_6606, plain, (![D_578]: (r2_hidden(k1_funct_1('#skF_17', D_578), '#skF_15') | ~r2_hidden(D_578, k1_relat_1('#skF_17')) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17'))), inference(resolution, [status(thm)], [c_105, c_6603])).
% 10.26/4.01  tff(c_6610, plain, (![D_579]: (r2_hidden(k1_funct_1('#skF_17', D_579), '#skF_15') | ~r2_hidden(D_579, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_6606])).
% 10.26/4.01  tff(c_6623, plain, (![D_579, B_2]: (r2_hidden(k1_funct_1('#skF_17', D_579), B_2) | ~r1_tarski('#skF_15', B_2) | ~r2_hidden(D_579, '#skF_15'))), inference(resolution, [status(thm)], [c_6610, c_2])).
% 10.26/4.01  tff(c_86, plain, (v1_relat_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_84, plain, (v1_funct_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_72, plain, (v2_funct_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_78, plain, (k1_relat_1('#skF_16')='#skF_15'), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_62, plain, (![A_157, C_159]: (r2_hidden(k4_tarski(A_157, k1_funct_1(C_159, A_157)), C_159) | ~r2_hidden(A_157, k1_relat_1(C_159)) | ~v1_funct_1(C_159) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.26/4.01  tff(c_70, plain, (k5_relat_1('#skF_17', '#skF_16')='#skF_16'), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.26/4.01  tff(c_7394, plain, (![D_639, B_640, A_641, E_642]: (r2_hidden(k4_tarski(D_639, '#skF_2'(B_640, k5_relat_1(A_641, B_640), D_639, A_641, E_642)), A_641) | ~r2_hidden(k4_tarski(D_639, E_642), k5_relat_1(A_641, B_640)) | ~v1_relat_1(k5_relat_1(A_641, B_640)) | ~v1_relat_1(B_640) | ~v1_relat_1(A_641))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.26/4.01  tff(c_7411, plain, (![D_639, E_642]: (r2_hidden(k4_tarski(D_639, '#skF_2'('#skF_16', '#skF_16', D_639, '#skF_17', E_642)), '#skF_17') | ~r2_hidden(k4_tarski(D_639, E_642), k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_7394])).
% 10.26/4.01  tff(c_7419, plain, (![D_643, E_644]: (r2_hidden(k4_tarski(D_643, '#skF_2'('#skF_16', '#skF_16', D_643, '#skF_17', E_644)), '#skF_17') | ~r2_hidden(k4_tarski(D_643, E_644), '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_86, c_70, c_70, c_7411])).
% 10.26/4.01  tff(c_64, plain, (![C_159, A_157, B_158]: (k1_funct_1(C_159, A_157)=B_158 | ~r2_hidden(k4_tarski(A_157, B_158), C_159) | ~v1_funct_1(C_159) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.26/4.01  tff(c_7427, plain, (![D_643, E_644]: (k1_funct_1('#skF_17', D_643)='#skF_2'('#skF_16', '#skF_16', D_643, '#skF_17', E_644) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17') | ~r2_hidden(k4_tarski(D_643, E_644), '#skF_16'))), inference(resolution, [status(thm)], [c_7419, c_64])).
% 10.26/4.01  tff(c_7460, plain, (![D_647, E_648]: (k1_funct_1('#skF_17', D_647)='#skF_2'('#skF_16', '#skF_16', D_647, '#skF_17', E_648) | ~r2_hidden(k4_tarski(D_647, E_648), '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_7427])).
% 10.26/4.01  tff(c_7472, plain, (![A_157]: ('#skF_2'('#skF_16', '#skF_16', A_157, '#skF_17', k1_funct_1('#skF_16', A_157))=k1_funct_1('#skF_17', A_157) | ~r2_hidden(A_157, k1_relat_1('#skF_16')) | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_62, c_7460])).
% 10.26/4.01  tff(c_7479, plain, (![A_157]: ('#skF_2'('#skF_16', '#skF_16', A_157, '#skF_17', k1_funct_1('#skF_16', A_157))=k1_funct_1('#skF_17', A_157) | ~r2_hidden(A_157, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_78, c_7472])).
% 10.26/4.01  tff(c_7690, plain, (![B_658, A_659, D_660, E_661]: (r2_hidden(k4_tarski('#skF_2'(B_658, k5_relat_1(A_659, B_658), D_660, A_659, E_661), E_661), B_658) | ~r2_hidden(k4_tarski(D_660, E_661), k5_relat_1(A_659, B_658)) | ~v1_relat_1(k5_relat_1(A_659, B_658)) | ~v1_relat_1(B_658) | ~v1_relat_1(A_659))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.26/4.01  tff(c_7719, plain, (![D_660, E_661]: (r2_hidden(k4_tarski('#skF_2'('#skF_16', '#skF_16', D_660, '#skF_17', E_661), E_661), '#skF_16') | ~r2_hidden(k4_tarski(D_660, E_661), k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_7690])).
% 10.26/4.01  tff(c_7734, plain, (![D_662, E_663]: (r2_hidden(k4_tarski('#skF_2'('#skF_16', '#skF_16', D_662, '#skF_17', E_663), E_663), '#skF_16') | ~r2_hidden(k4_tarski(D_662, E_663), '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_86, c_70, c_70, c_7719])).
% 10.26/4.01  tff(c_7748, plain, (![D_662, E_663]: (k1_funct_1('#skF_16', '#skF_2'('#skF_16', '#skF_16', D_662, '#skF_17', E_663))=E_663 | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16') | ~r2_hidden(k4_tarski(D_662, E_663), '#skF_16'))), inference(resolution, [status(thm)], [c_7734, c_64])).
% 10.26/4.01  tff(c_7822, plain, (![D_668, E_669]: (k1_funct_1('#skF_16', '#skF_2'('#skF_16', '#skF_16', D_668, '#skF_17', E_669))=E_669 | ~r2_hidden(k4_tarski(D_668, E_669), '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_7748])).
% 10.26/4.01  tff(c_7841, plain, (![A_157]: (k1_funct_1('#skF_16', '#skF_2'('#skF_16', '#skF_16', A_157, '#skF_17', k1_funct_1('#skF_16', A_157)))=k1_funct_1('#skF_16', A_157) | ~r2_hidden(A_157, k1_relat_1('#skF_16')) | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_62, c_7822])).
% 10.26/4.01  tff(c_7874, plain, (![A_673]: (k1_funct_1('#skF_16', '#skF_2'('#skF_16', '#skF_16', A_673, '#skF_17', k1_funct_1('#skF_16', A_673)))=k1_funct_1('#skF_16', A_673) | ~r2_hidden(A_673, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_78, c_7841])).
% 10.26/4.01  tff(c_7954, plain, (![A_674]: (k1_funct_1('#skF_16', k1_funct_1('#skF_17', A_674))=k1_funct_1('#skF_16', A_674) | ~r2_hidden(A_674, '#skF_15') | ~r2_hidden(A_674, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_7479, c_7874])).
% 10.26/4.01  tff(c_44, plain, (![C_151, B_150, A_145]: (C_151=B_150 | k1_funct_1(A_145, C_151)!=k1_funct_1(A_145, B_150) | ~r2_hidden(C_151, k1_relat_1(A_145)) | ~r2_hidden(B_150, k1_relat_1(A_145)) | ~v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.26/4.01  tff(c_7980, plain, (![A_674, C_151]: (k1_funct_1('#skF_17', A_674)=C_151 | k1_funct_1('#skF_16', C_151)!=k1_funct_1('#skF_16', A_674) | ~r2_hidden(C_151, k1_relat_1('#skF_16')) | ~r2_hidden(k1_funct_1('#skF_17', A_674), k1_relat_1('#skF_16')) | ~v2_funct_1('#skF_16') | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16') | ~r2_hidden(A_674, '#skF_15') | ~r2_hidden(A_674, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_7954, c_44])).
% 10.26/4.01  tff(c_8017, plain, (![A_674, C_151]: (k1_funct_1('#skF_17', A_674)=C_151 | k1_funct_1('#skF_16', C_151)!=k1_funct_1('#skF_16', A_674) | ~r2_hidden(C_151, '#skF_15') | ~r2_hidden(k1_funct_1('#skF_17', A_674), '#skF_15') | ~r2_hidden(A_674, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_72, c_78, c_78, c_7980])).
% 10.26/4.01  tff(c_17030, plain, (![A_1068]: (k1_funct_1('#skF_17', A_1068)=A_1068 | ~r2_hidden(A_1068, '#skF_15') | ~r2_hidden(k1_funct_1('#skF_17', A_1068), '#skF_15') | ~r2_hidden(A_1068, '#skF_15'))), inference(reflexivity, [status(thm), theory('equality')], [c_8017])).
% 10.26/4.01  tff(c_17047, plain, (![D_579]: (k1_funct_1('#skF_17', D_579)=D_579 | ~r1_tarski('#skF_15', '#skF_15') | ~r2_hidden(D_579, '#skF_15'))), inference(resolution, [status(thm)], [c_6623, c_17030])).
% 10.26/4.01  tff(c_17082, plain, (![D_1069]: (k1_funct_1('#skF_17', D_1069)=D_1069 | ~r2_hidden(D_1069, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_17047])).
% 10.26/4.01  tff(c_17408, plain, (k1_funct_1('#skF_17', '#skF_14'('#skF_15', '#skF_17'))='#skF_14'('#skF_15', '#skF_17') | ~r1_tarski('#skF_15', '#skF_15')), inference(resolution, [status(thm)], [c_245, c_17082])).
% 10.26/4.01  tff(c_17567, plain, (k1_funct_1('#skF_17', '#skF_14'('#skF_15', '#skF_17'))='#skF_14'('#skF_15', '#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_17408])).
% 10.26/4.01  tff(c_17569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6492, c_17567])).
% 10.26/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.26/4.01  
% 10.26/4.01  Inference rules
% 10.26/4.01  ----------------------
% 10.26/4.01  #Ref     : 5
% 10.26/4.01  #Sup     : 3739
% 10.26/4.01  #Fact    : 0
% 10.26/4.01  #Define  : 0
% 10.26/4.01  #Split   : 19
% 10.26/4.01  #Chain   : 0
% 10.26/4.01  #Close   : 0
% 10.26/4.02  
% 10.26/4.02  Ordering : KBO
% 10.26/4.02  
% 10.26/4.02  Simplification rules
% 10.26/4.02  ----------------------
% 10.26/4.02  #Subsume      : 1056
% 10.26/4.02  #Demod        : 3325
% 10.26/4.02  #Tautology    : 559
% 10.26/4.02  #SimpNegUnit  : 29
% 10.26/4.02  #BackRed      : 109
% 10.26/4.02  
% 10.26/4.02  #Partial instantiations: 0
% 10.26/4.02  #Strategies tried      : 1
% 10.26/4.02  
% 10.26/4.02  Timing (in seconds)
% 10.26/4.02  ----------------------
% 10.26/4.02  Preprocessing        : 0.38
% 10.26/4.02  Parsing              : 0.18
% 10.26/4.02  CNF conversion       : 0.04
% 10.26/4.02  Main loop            : 2.85
% 10.26/4.02  Inferencing          : 0.88
% 10.26/4.02  Reduction            : 0.82
% 10.26/4.02  Demodulation         : 0.55
% 10.26/4.02  BG Simplification    : 0.12
% 10.26/4.02  Subsumption          : 0.83
% 10.26/4.02  Abstraction          : 0.13
% 10.26/4.02  MUC search           : 0.00
% 10.26/4.02  Cooper               : 0.00
% 10.26/4.02  Total                : 3.27
% 10.26/4.02  Index Insertion      : 0.00
% 10.26/4.02  Index Deletion       : 0.00
% 10.26/4.02  Index Matching       : 0.00
% 10.26/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
