%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:01 EST 2020

% Result     : Theorem 9.68s
% Output     : CNFRefutation 9.82s
% Verified   : 
% Statistics : Number of formulae       :  130 (1071 expanded)
%              Number of leaves         :   35 ( 351 expanded)
%              Depth                    :   16
%              Number of atoms          :  336 (4282 expanded)
%              Number of equality atoms :   51 (1291 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_8 > #skF_3 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ~ ( ( B = k1_xboole_0
                 => A = k1_xboole_0 )
                & r1_partfun1(C,D)
                & ! [E] :
                    ( ( v1_funct_1(E)
                      & v1_funct_2(E,A,B)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => ~ ( r1_partfun1(C,E)
                        & r1_partfun1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_2)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ~ ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
              & r1_partfun1(C,D)
              & ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => ~ ( v1_partfun1(E,A)
                      & r1_partfun1(C,E)
                      & r1_partfun1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
          & ! [D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,A,B)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ~ r1_partfun1(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_98,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_102,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_100,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_96,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_92,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_94,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_123,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_1512,plain,(
    ! [B_253,A_254,C_255,D_256] :
      ( k1_xboole_0 = B_253
      | v1_funct_1('#skF_4'(A_254,B_253,C_255,D_256))
      | ~ r1_partfun1(C_255,D_256)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_1(D_256)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1521,plain,(
    ! [C_255] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_1('#skF_4'('#skF_5','#skF_6',C_255,'#skF_8'))
      | ~ r1_partfun1(C_255,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_255) ) ),
    inference(resolution,[status(thm)],[c_96,c_1512])).

tff(c_1537,plain,(
    ! [C_255] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_1('#skF_4'('#skF_5','#skF_6',C_255,'#skF_8'))
      | ~ r1_partfun1(C_255,'#skF_8')
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1521])).

tff(c_1657,plain,(
    ! [C_263] :
      ( v1_funct_1('#skF_4'('#skF_5','#skF_6',C_263,'#skF_8'))
      | ~ r1_partfun1(C_263,'#skF_8')
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_263) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1537])).

tff(c_1668,plain,
    ( v1_funct_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_1657])).

tff(c_1682,plain,(
    v1_funct_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92,c_1668])).

tff(c_1967,plain,(
    ! [B_277,C_278,A_279,D_280] :
      ( k1_xboole_0 = B_277
      | r1_partfun1(C_278,'#skF_4'(A_279,B_277,C_278,D_280))
      | ~ r1_partfun1(C_278,D_280)
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_279,B_277)))
      | ~ v1_funct_1(D_280)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_277)))
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1976,plain,(
    ! [C_278] :
      ( k1_xboole_0 = '#skF_6'
      | r1_partfun1(C_278,'#skF_4'('#skF_5','#skF_6',C_278,'#skF_8'))
      | ~ r1_partfun1(C_278,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_278) ) ),
    inference(resolution,[status(thm)],[c_96,c_1967])).

tff(c_1992,plain,(
    ! [C_278] :
      ( k1_xboole_0 = '#skF_6'
      | r1_partfun1(C_278,'#skF_4'('#skF_5','#skF_6',C_278,'#skF_8'))
      | ~ r1_partfun1(C_278,'#skF_8')
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1976])).

tff(c_2054,plain,(
    ! [C_283] :
      ( r1_partfun1(C_283,'#skF_4'('#skF_5','#skF_6',C_283,'#skF_8'))
      | ~ r1_partfun1(C_283,'#skF_8')
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1992])).

tff(c_2062,plain,
    ( r1_partfun1('#skF_7','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_2054])).

tff(c_2074,plain,(
    r1_partfun1('#skF_7','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92,c_2062])).

tff(c_1767,plain,(
    ! [B_266,D_267,A_268,C_269] :
      ( k1_xboole_0 = B_266
      | r1_partfun1(D_267,'#skF_4'(A_268,B_266,C_269,D_267))
      | ~ r1_partfun1(C_269,D_267)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(A_268,B_266)))
      | ~ v1_funct_1(D_267)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_268,B_266)))
      | ~ v1_funct_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1776,plain,(
    ! [C_269] :
      ( k1_xboole_0 = '#skF_6'
      | r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6',C_269,'#skF_8'))
      | ~ r1_partfun1(C_269,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_96,c_1767])).

tff(c_1792,plain,(
    ! [C_269] :
      ( k1_xboole_0 = '#skF_6'
      | r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6',C_269,'#skF_8'))
      | ~ r1_partfun1(C_269,'#skF_8')
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1776])).

tff(c_1898,plain,(
    ! [C_275] :
      ( r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6',C_275,'#skF_8'))
      | ~ r1_partfun1(C_275,'#skF_8')
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_275) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1792])).

tff(c_1909,plain,
    ( r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_1898])).

tff(c_1923,plain,(
    r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92,c_1909])).

tff(c_1624,plain,(
    ! [B_259,A_260,C_261,D_262] :
      ( k1_xboole_0 = B_259
      | v1_partfun1('#skF_4'(A_260,B_259,C_261,D_262),A_260)
      | ~ r1_partfun1(C_261,D_262)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_259)))
      | ~ v1_funct_1(D_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_260,B_259)))
      | ~ v1_funct_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1633,plain,(
    ! [C_261] :
      ( k1_xboole_0 = '#skF_6'
      | v1_partfun1('#skF_4'('#skF_5','#skF_6',C_261,'#skF_8'),'#skF_5')
      | ~ r1_partfun1(C_261,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_96,c_1624])).

tff(c_1649,plain,(
    ! [C_261] :
      ( k1_xboole_0 = '#skF_6'
      | v1_partfun1('#skF_4'('#skF_5','#skF_6',C_261,'#skF_8'),'#skF_5')
      | ~ r1_partfun1(C_261,'#skF_8')
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1633])).

tff(c_1801,plain,(
    ! [C_271] :
      ( v1_partfun1('#skF_4'('#skF_5','#skF_6',C_271,'#skF_8'),'#skF_5')
      | ~ r1_partfun1(C_271,'#skF_8')
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1649])).

tff(c_1812,plain,
    ( v1_partfun1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5')
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_1801])).

tff(c_1826,plain,(
    v1_partfun1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92,c_1812])).

tff(c_2157,plain,(
    ! [B_290,A_291,C_292,D_293] :
      ( k1_xboole_0 = B_290
      | m1_subset_1('#skF_4'(A_291,B_290,C_292,D_293),k1_zfmisc_1(k2_zfmisc_1(A_291,B_290)))
      | ~ r1_partfun1(C_292,D_293)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_290)))
      | ~ v1_funct_1(D_293)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_291,B_290)))
      | ~ v1_funct_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_funct_2(C_24,A_22,B_23)
      | ~ v1_partfun1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7098,plain,(
    ! [A_679,B_680,C_681,D_682] :
      ( v1_funct_2('#skF_4'(A_679,B_680,C_681,D_682),A_679,B_680)
      | ~ v1_partfun1('#skF_4'(A_679,B_680,C_681,D_682),A_679)
      | ~ v1_funct_1('#skF_4'(A_679,B_680,C_681,D_682))
      | k1_xboole_0 = B_680
      | ~ r1_partfun1(C_681,D_682)
      | ~ m1_subset_1(D_682,k1_zfmisc_1(k2_zfmisc_1(A_679,B_680)))
      | ~ v1_funct_1(D_682)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(A_679,B_680)))
      | ~ v1_funct_1(C_681) ) ),
    inference(resolution,[status(thm)],[c_2157,c_44])).

tff(c_7109,plain,(
    ! [C_681] :
      ( v1_funct_2('#skF_4'('#skF_5','#skF_6',C_681,'#skF_8'),'#skF_5','#skF_6')
      | ~ v1_partfun1('#skF_4'('#skF_5','#skF_6',C_681,'#skF_8'),'#skF_5')
      | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6',C_681,'#skF_8'))
      | k1_xboole_0 = '#skF_6'
      | ~ r1_partfun1(C_681,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_681) ) ),
    inference(resolution,[status(thm)],[c_96,c_7098])).

tff(c_7126,plain,(
    ! [C_681] :
      ( v1_funct_2('#skF_4'('#skF_5','#skF_6',C_681,'#skF_8'),'#skF_5','#skF_6')
      | ~ v1_partfun1('#skF_4'('#skF_5','#skF_6',C_681,'#skF_8'),'#skF_5')
      | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6',C_681,'#skF_8'))
      | k1_xboole_0 = '#skF_6'
      | ~ r1_partfun1(C_681,'#skF_8')
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_681) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_7109])).

tff(c_7174,plain,(
    ! [C_685] :
      ( v1_funct_2('#skF_4'('#skF_5','#skF_6',C_685,'#skF_8'),'#skF_5','#skF_6')
      | ~ v1_partfun1('#skF_4'('#skF_5','#skF_6',C_685,'#skF_8'),'#skF_5')
      | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6',C_685,'#skF_8'))
      | ~ r1_partfun1(C_685,'#skF_8')
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_685) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_7126])).

tff(c_7189,plain,
    ( v1_funct_2('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5')
    | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_7174])).

tff(c_7206,plain,(
    v1_funct_2('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92,c_1682,c_1826,c_7189])).

tff(c_90,plain,(
    ! [E_51] :
      ( ~ r1_partfun1('#skF_8',E_51)
      | ~ r1_partfun1('#skF_7',E_51)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_2(E_51,'#skF_5','#skF_6')
      | ~ v1_funct_1(E_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2223,plain,(
    ! [C_292,D_293] :
      ( ~ r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6',C_292,D_293))
      | ~ r1_partfun1('#skF_7','#skF_4'('#skF_5','#skF_6',C_292,D_293))
      | ~ v1_funct_2('#skF_4'('#skF_5','#skF_6',C_292,D_293),'#skF_5','#skF_6')
      | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6',C_292,D_293))
      | k1_xboole_0 = '#skF_6'
      | ~ r1_partfun1(C_292,D_293)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(D_293)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_292) ) ),
    inference(resolution,[status(thm)],[c_2157,c_90])).

tff(c_8140,plain,(
    ! [C_730,D_731] :
      ( ~ r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6',C_730,D_731))
      | ~ r1_partfun1('#skF_7','#skF_4'('#skF_5','#skF_6',C_730,D_731))
      | ~ v1_funct_2('#skF_4'('#skF_5','#skF_6',C_730,D_731),'#skF_5','#skF_6')
      | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6',C_730,D_731))
      | ~ r1_partfun1(C_730,D_731)
      | ~ m1_subset_1(D_731,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(D_731)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_2223])).

tff(c_8144,plain,
    ( ~ r1_partfun1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_7','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7206,c_8140])).

tff(c_8153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_96,c_92,c_1682,c_2074,c_1923,c_8144])).

tff(c_8155,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8185,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_6',B_6) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8155,c_8155,c_16])).

tff(c_8154,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_8163,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8155,c_8154])).

tff(c_8217,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8185,c_8163,c_96])).

tff(c_8241,plain,(
    ! [A_742,B_743] :
      ( r1_tarski(A_742,B_743)
      | ~ m1_subset_1(A_742,k1_zfmisc_1(B_743)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8251,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_8217,c_8241])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8219,plain,(
    ! [A_4] :
      ( A_4 = '#skF_6'
      | ~ r1_tarski(A_4,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8155,c_8155,c_10])).

tff(c_8258,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8251,c_8219])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8194,plain,(
    ! [A_11] : m1_subset_1('#skF_6',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8155,c_22])).

tff(c_8266,plain,(
    ! [A_11] : m1_subset_1('#skF_8',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8194])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8156,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8154,c_8])).

tff(c_8173,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8163,c_8156])).

tff(c_8270,plain,(
    ! [A_3] : r1_tarski('#skF_8',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8173])).

tff(c_8272,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8155])).

tff(c_58,plain,(
    ! [B_36,C_37] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_36,C_37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_103,plain,(
    ! [B_36,C_37] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_36,C_37),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_58])).

tff(c_8500,plain,(
    ! [B_779,C_780] :
      ( m1_subset_1('#skF_3'('#skF_8',B_779,C_780),k1_zfmisc_1('#skF_8'))
      | ~ m1_subset_1(C_780,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_780) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8272,c_8272,c_8272,c_103])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8528,plain,(
    ! [B_783,C_784] :
      ( r1_tarski('#skF_3'('#skF_8',B_783,C_784),'#skF_8')
      | ~ m1_subset_1(C_784,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_784) ) ),
    inference(resolution,[status(thm)],[c_8500,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8533,plain,(
    ! [B_783,C_784] :
      ( '#skF_3'('#skF_8',B_783,C_784) = '#skF_8'
      | ~ r1_tarski('#skF_8','#skF_3'('#skF_8',B_783,C_784))
      | ~ m1_subset_1(C_784,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_784) ) ),
    inference(resolution,[status(thm)],[c_8528,c_2])).

tff(c_8544,plain,(
    ! [B_785,C_786] :
      ( '#skF_3'('#skF_8',B_785,C_786) = '#skF_8'
      | ~ m1_subset_1(C_786,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_786) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8270,c_8533])).

tff(c_8549,plain,(
    ! [B_785] :
      ( '#skF_3'('#skF_8',B_785,'#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8266,c_8544])).

tff(c_8560,plain,(
    ! [B_787] : '#skF_3'('#skF_8',B_787,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8549])).

tff(c_62,plain,(
    ! [B_36,C_37] :
      ( v1_funct_2('#skF_3'(k1_xboole_0,B_36,C_37),k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_111,plain,(
    ! [B_36,C_37] :
      ( v1_funct_2('#skF_3'(k1_xboole_0,B_36,C_37),k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_8521,plain,(
    ! [B_36,C_37] :
      ( v1_funct_2('#skF_3'('#skF_8',B_36,C_37),'#skF_8',B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8272,c_8272,c_8272,c_111])).

tff(c_8568,plain,(
    ! [B_787] :
      ( v1_funct_2('#skF_8','#skF_8',B_787)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8560,c_8521])).

tff(c_8584,plain,(
    ! [B_787] : v1_funct_2('#skF_8','#skF_8',B_787) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8266,c_8568])).

tff(c_8172,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8163,c_100])).

tff(c_8186,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8185,c_8172])).

tff(c_8252,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_8186,c_8241])).

tff(c_8289,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8252])).

tff(c_8356,plain,(
    ! [A_752] :
      ( A_752 = '#skF_8'
      | ~ r1_tarski(A_752,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_8219])).

tff(c_8370,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8289,c_8356])).

tff(c_8375,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8370,c_92])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8196,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8155,c_8155,c_14])).

tff(c_8265,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_8196])).

tff(c_8271,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8163])).

tff(c_8278,plain,(
    ! [E_51] :
      ( ~ r1_partfun1('#skF_8',E_51)
      | ~ r1_partfun1('#skF_7',E_51)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_8')))
      | ~ v1_funct_2(E_51,'#skF_5','#skF_8')
      | ~ v1_funct_1(E_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_90])).

tff(c_8284,plain,(
    ! [E_51] :
      ( ~ r1_partfun1('#skF_8',E_51)
      | ~ r1_partfun1('#skF_7',E_51)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8')))
      | ~ v1_funct_2(E_51,'#skF_8','#skF_8')
      | ~ v1_funct_1(E_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8271,c_8271,c_8278])).

tff(c_8428,plain,(
    ! [E_759] :
      ( ~ r1_partfun1('#skF_8',E_759)
      | ~ r1_partfun1('#skF_8',E_759)
      | ~ m1_subset_1(E_759,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_759,'#skF_8','#skF_8')
      | ~ v1_funct_1(E_759) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8265,c_8370,c_8284])).

tff(c_8432,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ v1_funct_2('#skF_8','#skF_8','#skF_8')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8266,c_8428])).

tff(c_8439,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8375,c_8432])).

tff(c_8605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8584,c_8439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.68/3.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.82/3.44  
% 9.82/3.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.82/3.44  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_8 > #skF_3 > #skF_2
% 9.82/3.44  
% 9.82/3.44  %Foreground sorts:
% 9.82/3.44  
% 9.82/3.44  
% 9.82/3.44  %Background operators:
% 9.82/3.44  
% 9.82/3.44  
% 9.82/3.44  %Foreground operators:
% 9.82/3.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.82/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.82/3.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.82/3.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.82/3.44  tff('#skF_7', type, '#skF_7': $i).
% 9.82/3.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.82/3.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.82/3.44  tff('#skF_5', type, '#skF_5': $i).
% 9.82/3.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.82/3.44  tff('#skF_6', type, '#skF_6': $i).
% 9.82/3.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.82/3.44  tff('#skF_1', type, '#skF_1': $i).
% 9.82/3.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.82/3.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.82/3.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 9.82/3.44  tff('#skF_8', type, '#skF_8': $i).
% 9.82/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.82/3.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.82/3.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.82/3.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.82/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.82/3.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.82/3.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.82/3.44  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 9.82/3.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.82/3.44  
% 9.82/3.46  tff(f_186, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((((B = k1_xboole_0) => (A = k1_xboole_0)) & r1_partfun1(C, D)) & (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r1_partfun1(C, E) & r1_partfun1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_2)).
% 9.82/3.46  tff(f_157, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((((B = k1_xboole_0) => (A = k1_xboole_0)) & r1_partfun1(C, D)) & (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((v1_partfun1(E, A) & r1_partfun1(C, E)) & r1_partfun1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_partfun1)).
% 9.82/3.46  tff(f_92, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_funct_2)).
% 9.82/3.46  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.82/3.46  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.82/3.46  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.82/3.46  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.82/3.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.82/3.46  tff(f_129, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(((B = k1_xboole_0) => (A = k1_xboole_0)) & (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~r1_partfun1(C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_2)).
% 9.82/3.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.82/3.46  tff(c_98, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_102, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_100, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_96, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_92, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_94, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_123, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_94])).
% 9.82/3.46  tff(c_1512, plain, (![B_253, A_254, C_255, D_256]: (k1_xboole_0=B_253 | v1_funct_1('#skF_4'(A_254, B_253, C_255, D_256)) | ~r1_partfun1(C_255, D_256) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_1(D_256) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_1(C_255))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.82/3.46  tff(c_1521, plain, (![C_255]: (k1_xboole_0='#skF_6' | v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_255, '#skF_8')) | ~r1_partfun1(C_255, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_255))), inference(resolution, [status(thm)], [c_96, c_1512])).
% 9.82/3.46  tff(c_1537, plain, (![C_255]: (k1_xboole_0='#skF_6' | v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_255, '#skF_8')) | ~r1_partfun1(C_255, '#skF_8') | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_255))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1521])).
% 9.82/3.46  tff(c_1657, plain, (![C_263]: (v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_263, '#skF_8')) | ~r1_partfun1(C_263, '#skF_8') | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_263))), inference(negUnitSimplification, [status(thm)], [c_123, c_1537])).
% 9.82/3.46  tff(c_1668, plain, (v1_funct_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_100, c_1657])).
% 9.82/3.46  tff(c_1682, plain, (v1_funct_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92, c_1668])).
% 9.82/3.46  tff(c_1967, plain, (![B_277, C_278, A_279, D_280]: (k1_xboole_0=B_277 | r1_partfun1(C_278, '#skF_4'(A_279, B_277, C_278, D_280)) | ~r1_partfun1(C_278, D_280) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_279, B_277))) | ~v1_funct_1(D_280) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_277))) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.82/3.46  tff(c_1976, plain, (![C_278]: (k1_xboole_0='#skF_6' | r1_partfun1(C_278, '#skF_4'('#skF_5', '#skF_6', C_278, '#skF_8')) | ~r1_partfun1(C_278, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_278))), inference(resolution, [status(thm)], [c_96, c_1967])).
% 9.82/3.46  tff(c_1992, plain, (![C_278]: (k1_xboole_0='#skF_6' | r1_partfun1(C_278, '#skF_4'('#skF_5', '#skF_6', C_278, '#skF_8')) | ~r1_partfun1(C_278, '#skF_8') | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_278))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1976])).
% 9.82/3.46  tff(c_2054, plain, (![C_283]: (r1_partfun1(C_283, '#skF_4'('#skF_5', '#skF_6', C_283, '#skF_8')) | ~r1_partfun1(C_283, '#skF_8') | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_283))), inference(negUnitSimplification, [status(thm)], [c_123, c_1992])).
% 9.82/3.46  tff(c_2062, plain, (r1_partfun1('#skF_7', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_100, c_2054])).
% 9.82/3.46  tff(c_2074, plain, (r1_partfun1('#skF_7', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92, c_2062])).
% 9.82/3.46  tff(c_1767, plain, (![B_266, D_267, A_268, C_269]: (k1_xboole_0=B_266 | r1_partfun1(D_267, '#skF_4'(A_268, B_266, C_269, D_267)) | ~r1_partfun1(C_269, D_267) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(A_268, B_266))) | ~v1_funct_1(D_267) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_268, B_266))) | ~v1_funct_1(C_269))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.82/3.46  tff(c_1776, plain, (![C_269]: (k1_xboole_0='#skF_6' | r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', C_269, '#skF_8')) | ~r1_partfun1(C_269, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_269))), inference(resolution, [status(thm)], [c_96, c_1767])).
% 9.82/3.46  tff(c_1792, plain, (![C_269]: (k1_xboole_0='#skF_6' | r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', C_269, '#skF_8')) | ~r1_partfun1(C_269, '#skF_8') | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_269))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1776])).
% 9.82/3.46  tff(c_1898, plain, (![C_275]: (r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', C_275, '#skF_8')) | ~r1_partfun1(C_275, '#skF_8') | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_275))), inference(negUnitSimplification, [status(thm)], [c_123, c_1792])).
% 9.82/3.46  tff(c_1909, plain, (r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_100, c_1898])).
% 9.82/3.46  tff(c_1923, plain, (r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92, c_1909])).
% 9.82/3.46  tff(c_1624, plain, (![B_259, A_260, C_261, D_262]: (k1_xboole_0=B_259 | v1_partfun1('#skF_4'(A_260, B_259, C_261, D_262), A_260) | ~r1_partfun1(C_261, D_262) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_259))) | ~v1_funct_1(D_262) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_260, B_259))) | ~v1_funct_1(C_261))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.82/3.46  tff(c_1633, plain, (![C_261]: (k1_xboole_0='#skF_6' | v1_partfun1('#skF_4'('#skF_5', '#skF_6', C_261, '#skF_8'), '#skF_5') | ~r1_partfun1(C_261, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_261))), inference(resolution, [status(thm)], [c_96, c_1624])).
% 9.82/3.46  tff(c_1649, plain, (![C_261]: (k1_xboole_0='#skF_6' | v1_partfun1('#skF_4'('#skF_5', '#skF_6', C_261, '#skF_8'), '#skF_5') | ~r1_partfun1(C_261, '#skF_8') | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_261))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1633])).
% 9.82/3.46  tff(c_1801, plain, (![C_271]: (v1_partfun1('#skF_4'('#skF_5', '#skF_6', C_271, '#skF_8'), '#skF_5') | ~r1_partfun1(C_271, '#skF_8') | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_271))), inference(negUnitSimplification, [status(thm)], [c_123, c_1649])).
% 9.82/3.46  tff(c_1812, plain, (v1_partfun1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5') | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_100, c_1801])).
% 9.82/3.46  tff(c_1826, plain, (v1_partfun1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92, c_1812])).
% 9.82/3.46  tff(c_2157, plain, (![B_290, A_291, C_292, D_293]: (k1_xboole_0=B_290 | m1_subset_1('#skF_4'(A_291, B_290, C_292, D_293), k1_zfmisc_1(k2_zfmisc_1(A_291, B_290))) | ~r1_partfun1(C_292, D_293) | ~m1_subset_1(D_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_290))) | ~v1_funct_1(D_293) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_291, B_290))) | ~v1_funct_1(C_292))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.82/3.46  tff(c_44, plain, (![C_24, A_22, B_23]: (v1_funct_2(C_24, A_22, B_23) | ~v1_partfun1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.82/3.46  tff(c_7098, plain, (![A_679, B_680, C_681, D_682]: (v1_funct_2('#skF_4'(A_679, B_680, C_681, D_682), A_679, B_680) | ~v1_partfun1('#skF_4'(A_679, B_680, C_681, D_682), A_679) | ~v1_funct_1('#skF_4'(A_679, B_680, C_681, D_682)) | k1_xboole_0=B_680 | ~r1_partfun1(C_681, D_682) | ~m1_subset_1(D_682, k1_zfmisc_1(k2_zfmisc_1(A_679, B_680))) | ~v1_funct_1(D_682) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(A_679, B_680))) | ~v1_funct_1(C_681))), inference(resolution, [status(thm)], [c_2157, c_44])).
% 9.82/3.46  tff(c_7109, plain, (![C_681]: (v1_funct_2('#skF_4'('#skF_5', '#skF_6', C_681, '#skF_8'), '#skF_5', '#skF_6') | ~v1_partfun1('#skF_4'('#skF_5', '#skF_6', C_681, '#skF_8'), '#skF_5') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_681, '#skF_8')) | k1_xboole_0='#skF_6' | ~r1_partfun1(C_681, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_681))), inference(resolution, [status(thm)], [c_96, c_7098])).
% 9.82/3.46  tff(c_7126, plain, (![C_681]: (v1_funct_2('#skF_4'('#skF_5', '#skF_6', C_681, '#skF_8'), '#skF_5', '#skF_6') | ~v1_partfun1('#skF_4'('#skF_5', '#skF_6', C_681, '#skF_8'), '#skF_5') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_681, '#skF_8')) | k1_xboole_0='#skF_6' | ~r1_partfun1(C_681, '#skF_8') | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_681))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_7109])).
% 9.82/3.46  tff(c_7174, plain, (![C_685]: (v1_funct_2('#skF_4'('#skF_5', '#skF_6', C_685, '#skF_8'), '#skF_5', '#skF_6') | ~v1_partfun1('#skF_4'('#skF_5', '#skF_6', C_685, '#skF_8'), '#skF_5') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_685, '#skF_8')) | ~r1_partfun1(C_685, '#skF_8') | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_685))), inference(negUnitSimplification, [status(thm)], [c_123, c_7126])).
% 9.82/3.46  tff(c_7189, plain, (v1_funct_2('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5', '#skF_6') | ~v1_partfun1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_100, c_7174])).
% 9.82/3.46  tff(c_7206, plain, (v1_funct_2('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92, c_1682, c_1826, c_7189])).
% 9.82/3.46  tff(c_90, plain, (![E_51]: (~r1_partfun1('#skF_8', E_51) | ~r1_partfun1('#skF_7', E_51) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2(E_51, '#skF_5', '#skF_6') | ~v1_funct_1(E_51))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.82/3.46  tff(c_2223, plain, (![C_292, D_293]: (~r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', C_292, D_293)) | ~r1_partfun1('#skF_7', '#skF_4'('#skF_5', '#skF_6', C_292, D_293)) | ~v1_funct_2('#skF_4'('#skF_5', '#skF_6', C_292, D_293), '#skF_5', '#skF_6') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_292, D_293)) | k1_xboole_0='#skF_6' | ~r1_partfun1(C_292, D_293) | ~m1_subset_1(D_293, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(D_293) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_292))), inference(resolution, [status(thm)], [c_2157, c_90])).
% 9.82/3.46  tff(c_8140, plain, (![C_730, D_731]: (~r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', C_730, D_731)) | ~r1_partfun1('#skF_7', '#skF_4'('#skF_5', '#skF_6', C_730, D_731)) | ~v1_funct_2('#skF_4'('#skF_5', '#skF_6', C_730, D_731), '#skF_5', '#skF_6') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', C_730, D_731)) | ~r1_partfun1(C_730, D_731) | ~m1_subset_1(D_731, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(D_731) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_730))), inference(negUnitSimplification, [status(thm)], [c_123, c_2223])).
% 9.82/3.46  tff(c_8144, plain, (~r1_partfun1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_7', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_7206, c_8140])).
% 9.82/3.46  tff(c_8153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_96, c_92, c_1682, c_2074, c_1923, c_8144])).
% 9.82/3.46  tff(c_8155, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_94])).
% 9.82/3.46  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.82/3.46  tff(c_8185, plain, (![B_6]: (k2_zfmisc_1('#skF_6', B_6)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8155, c_8155, c_16])).
% 9.82/3.46  tff(c_8154, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_94])).
% 9.82/3.46  tff(c_8163, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8155, c_8154])).
% 9.82/3.46  tff(c_8217, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8185, c_8163, c_96])).
% 9.82/3.46  tff(c_8241, plain, (![A_742, B_743]: (r1_tarski(A_742, B_743) | ~m1_subset_1(A_742, k1_zfmisc_1(B_743)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.82/3.46  tff(c_8251, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_8217, c_8241])).
% 9.82/3.46  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.82/3.46  tff(c_8219, plain, (![A_4]: (A_4='#skF_6' | ~r1_tarski(A_4, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8155, c_8155, c_10])).
% 9.82/3.46  tff(c_8258, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_8251, c_8219])).
% 9.82/3.46  tff(c_22, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.82/3.46  tff(c_8194, plain, (![A_11]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_8155, c_22])).
% 9.82/3.46  tff(c_8266, plain, (![A_11]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8194])).
% 9.82/3.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.82/3.46  tff(c_8156, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8154, c_8])).
% 9.82/3.46  tff(c_8173, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8163, c_8156])).
% 9.82/3.46  tff(c_8270, plain, (![A_3]: (r1_tarski('#skF_8', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8173])).
% 9.82/3.46  tff(c_8272, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8155])).
% 9.82/3.46  tff(c_58, plain, (![B_36, C_37]: (m1_subset_1('#skF_3'(k1_xboole_0, B_36, C_37), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.82/3.46  tff(c_103, plain, (![B_36, C_37]: (m1_subset_1('#skF_3'(k1_xboole_0, B_36, C_37), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_58])).
% 9.82/3.46  tff(c_8500, plain, (![B_779, C_780]: (m1_subset_1('#skF_3'('#skF_8', B_779, C_780), k1_zfmisc_1('#skF_8')) | ~m1_subset_1(C_780, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_780))), inference(demodulation, [status(thm), theory('equality')], [c_8272, c_8272, c_8272, c_103])).
% 9.82/3.46  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.82/3.46  tff(c_8528, plain, (![B_783, C_784]: (r1_tarski('#skF_3'('#skF_8', B_783, C_784), '#skF_8') | ~m1_subset_1(C_784, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_784))), inference(resolution, [status(thm)], [c_8500, c_24])).
% 9.82/3.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.82/3.46  tff(c_8533, plain, (![B_783, C_784]: ('#skF_3'('#skF_8', B_783, C_784)='#skF_8' | ~r1_tarski('#skF_8', '#skF_3'('#skF_8', B_783, C_784)) | ~m1_subset_1(C_784, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_784))), inference(resolution, [status(thm)], [c_8528, c_2])).
% 9.82/3.46  tff(c_8544, plain, (![B_785, C_786]: ('#skF_3'('#skF_8', B_785, C_786)='#skF_8' | ~m1_subset_1(C_786, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_786))), inference(demodulation, [status(thm), theory('equality')], [c_8270, c_8533])).
% 9.82/3.46  tff(c_8549, plain, (![B_785]: ('#skF_3'('#skF_8', B_785, '#skF_8')='#skF_8' | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_8266, c_8544])).
% 9.82/3.46  tff(c_8560, plain, (![B_787]: ('#skF_3'('#skF_8', B_787, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8549])).
% 9.82/3.46  tff(c_62, plain, (![B_36, C_37]: (v1_funct_2('#skF_3'(k1_xboole_0, B_36, C_37), k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.82/3.46  tff(c_111, plain, (![B_36, C_37]: (v1_funct_2('#skF_3'(k1_xboole_0, B_36, C_37), k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 9.82/3.46  tff(c_8521, plain, (![B_36, C_37]: (v1_funct_2('#skF_3'('#skF_8', B_36, C_37), '#skF_8', B_36) | ~m1_subset_1(C_37, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_8272, c_8272, c_8272, c_111])).
% 9.82/3.46  tff(c_8568, plain, (![B_787]: (v1_funct_2('#skF_8', '#skF_8', B_787) | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8560, c_8521])).
% 9.82/3.46  tff(c_8584, plain, (![B_787]: (v1_funct_2('#skF_8', '#skF_8', B_787))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8266, c_8568])).
% 9.82/3.46  tff(c_8172, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_8163, c_100])).
% 9.82/3.46  tff(c_8186, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8185, c_8172])).
% 9.82/3.46  tff(c_8252, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_8186, c_8241])).
% 9.82/3.46  tff(c_8289, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8252])).
% 9.82/3.46  tff(c_8356, plain, (![A_752]: (A_752='#skF_8' | ~r1_tarski(A_752, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_8219])).
% 9.82/3.46  tff(c_8370, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_8289, c_8356])).
% 9.82/3.46  tff(c_8375, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8370, c_92])).
% 9.82/3.46  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.82/3.46  tff(c_8196, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8155, c_8155, c_14])).
% 9.82/3.46  tff(c_8265, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_8196])).
% 9.82/3.46  tff(c_8271, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8163])).
% 9.82/3.46  tff(c_8278, plain, (![E_51]: (~r1_partfun1('#skF_8', E_51) | ~r1_partfun1('#skF_7', E_51) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_8'))) | ~v1_funct_2(E_51, '#skF_5', '#skF_8') | ~v1_funct_1(E_51))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_90])).
% 9.82/3.46  tff(c_8284, plain, (![E_51]: (~r1_partfun1('#skF_8', E_51) | ~r1_partfun1('#skF_7', E_51) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))) | ~v1_funct_2(E_51, '#skF_8', '#skF_8') | ~v1_funct_1(E_51))), inference(demodulation, [status(thm), theory('equality')], [c_8271, c_8271, c_8278])).
% 9.82/3.46  tff(c_8428, plain, (![E_759]: (~r1_partfun1('#skF_8', E_759) | ~r1_partfun1('#skF_8', E_759) | ~m1_subset_1(E_759, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_759, '#skF_8', '#skF_8') | ~v1_funct_1(E_759))), inference(demodulation, [status(thm), theory('equality')], [c_8265, c_8370, c_8284])).
% 9.82/3.46  tff(c_8432, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~v1_funct_2('#skF_8', '#skF_8', '#skF_8') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_8266, c_8428])).
% 9.82/3.46  tff(c_8439, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8375, c_8432])).
% 9.82/3.46  tff(c_8605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8584, c_8439])).
% 9.82/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.82/3.46  
% 9.82/3.46  Inference rules
% 9.82/3.46  ----------------------
% 9.82/3.46  #Ref     : 3
% 9.82/3.46  #Sup     : 1776
% 9.82/3.46  #Fact    : 0
% 9.82/3.46  #Define  : 0
% 9.82/3.46  #Split   : 30
% 9.82/3.46  #Chain   : 0
% 9.82/3.46  #Close   : 0
% 9.82/3.46  
% 9.82/3.46  Ordering : KBO
% 9.82/3.46  
% 9.82/3.46  Simplification rules
% 9.82/3.46  ----------------------
% 9.82/3.46  #Subsume      : 383
% 9.82/3.46  #Demod        : 3244
% 9.82/3.46  #Tautology    : 733
% 9.82/3.46  #SimpNegUnit  : 144
% 9.82/3.46  #BackRed      : 28
% 9.82/3.46  
% 9.82/3.46  #Partial instantiations: 0
% 9.82/3.46  #Strategies tried      : 1
% 9.82/3.46  
% 9.82/3.46  Timing (in seconds)
% 9.82/3.46  ----------------------
% 9.82/3.46  Preprocessing        : 0.38
% 9.82/3.46  Parsing              : 0.19
% 9.82/3.47  CNF conversion       : 0.03
% 9.82/3.47  Main loop            : 2.30
% 9.82/3.47  Inferencing          : 0.65
% 9.82/3.47  Reduction            : 0.77
% 9.82/3.47  Demodulation         : 0.56
% 9.82/3.47  BG Simplification    : 0.07
% 9.82/3.47  Subsumption          : 0.71
% 9.82/3.47  Abstraction          : 0.07
% 9.82/3.47  MUC search           : 0.00
% 9.82/3.47  Cooper               : 0.00
% 9.82/3.47  Total                : 2.73
% 9.82/3.47  Index Insertion      : 0.00
% 9.82/3.47  Index Deletion       : 0.00
% 9.82/3.47  Index Matching       : 0.00
% 9.82/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
