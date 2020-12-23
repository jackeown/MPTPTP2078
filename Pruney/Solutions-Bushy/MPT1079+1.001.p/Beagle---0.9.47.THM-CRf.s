%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:22 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 194 expanded)
%              Number of leaves         :   34 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  286 ( 785 expanded)
%              Number of equality atoms :   24 (  76 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_funct_2 > k4_funct_2 > k3_funct_2 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_funct_2,type,(
    k4_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k5_funct_2,type,(
    k5_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => k3_funct_2(A,k2_zfmisc_1(B,C),D,E) = k4_tarski(k3_funct_2(A,B,k4_funct_2(A,B,C,D),E),k3_funct_2(A,C,k5_funct_2(A,B,C,D),E)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_funct_2)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => ( v1_funct_1(k4_funct_2(A,B,C,D))
        & v1_funct_2(k4_funct_2(A,B,C,D),A,B)
        & m1_subset_1(k4_funct_2(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,A,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                     => ( E = k4_funct_2(A,B,C,D)
                      <=> ! [F] :
                            ( m1_subset_1(F,A)
                           => k3_funct_2(A,B,E,F) = k1_mcart_1(k3_funct_2(A,k2_zfmisc_1(B,C),D,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_funct_2)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => ( v1_funct_1(k5_funct_2(A,B,C,D))
        & v1_funct_2(k5_funct_2(A,B,C,D),A,C)
        & m1_subset_1(k5_funct_2(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,A,C)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                     => ( E = k5_funct_2(A,B,C,D)
                      <=> ! [F] :
                            ( m1_subset_1(F,A)
                           => k3_funct_2(A,C,E,F) = k2_mcart_1(k3_funct_2(A,k2_zfmisc_1(B,C),D,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_funct_2)).

tff(f_154,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_166,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_160,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_109,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( v1_funct_1(k4_funct_2(A_255,B_256,C_257,D_258))
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_255,k2_zfmisc_1(B_256,C_257))))
      | ~ v1_funct_2(D_258,A_255,k2_zfmisc_1(B_256,C_257))
      | ~ v1_funct_1(D_258)
      | v1_xboole_0(C_257)
      | v1_xboole_0(B_256)
      | v1_xboole_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_112,plain,
    ( v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_115,plain,
    ( v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_112])).

tff(c_116,plain,(
    v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_115])).

tff(c_124,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( v1_funct_2(k4_funct_2(A_263,B_264,C_265,D_266),A_263,B_264)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(A_263,k2_zfmisc_1(B_264,C_265))))
      | ~ v1_funct_2(D_266,A_263,k2_zfmisc_1(B_264,C_265))
      | ~ v1_funct_1(D_266)
      | v1_xboole_0(C_265)
      | v1_xboole_0(B_264)
      | v1_xboole_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_126,plain,
    ( v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_129,plain,
    ( v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_126])).

tff(c_130,plain,(
    v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_129])).

tff(c_16,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( m1_subset_1(k4_funct_2(A_193,B_194,C_195,D_196),k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(A_193,k2_zfmisc_1(B_194,C_195))))
      | ~ v1_funct_2(D_196,A_193,k2_zfmisc_1(B_194,C_195))
      | ~ v1_funct_1(D_196)
      | v1_xboole_0(C_195)
      | v1_xboole_0(B_194)
      | v1_xboole_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_310,plain,(
    ! [C_349,A_350,F_351,D_348,B_347] :
      ( k3_funct_2(A_350,B_347,k4_funct_2(A_350,B_347,C_349,D_348),F_351) = k1_mcart_1(k3_funct_2(A_350,k2_zfmisc_1(B_347,C_349),D_348,F_351))
      | ~ m1_subset_1(F_351,A_350)
      | ~ m1_subset_1(k4_funct_2(A_350,B_347,C_349,D_348),k1_zfmisc_1(k2_zfmisc_1(A_350,B_347)))
      | ~ v1_funct_2(k4_funct_2(A_350,B_347,C_349,D_348),A_350,B_347)
      | ~ v1_funct_1(k4_funct_2(A_350,B_347,C_349,D_348))
      | ~ m1_subset_1(D_348,k1_zfmisc_1(k2_zfmisc_1(A_350,k2_zfmisc_1(B_347,C_349))))
      | ~ v1_funct_2(D_348,A_350,k2_zfmisc_1(B_347,C_349))
      | ~ v1_funct_1(D_348)
      | v1_xboole_0(C_349)
      | v1_xboole_0(B_347)
      | v1_xboole_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_355,plain,(
    ! [D_361,B_360,A_362,C_363,F_364] :
      ( k3_funct_2(A_362,B_360,k4_funct_2(A_362,B_360,C_363,D_361),F_364) = k1_mcart_1(k3_funct_2(A_362,k2_zfmisc_1(B_360,C_363),D_361,F_364))
      | ~ m1_subset_1(F_364,A_362)
      | ~ v1_funct_2(k4_funct_2(A_362,B_360,C_363,D_361),A_362,B_360)
      | ~ v1_funct_1(k4_funct_2(A_362,B_360,C_363,D_361))
      | ~ m1_subset_1(D_361,k1_zfmisc_1(k2_zfmisc_1(A_362,k2_zfmisc_1(B_360,C_363))))
      | ~ v1_funct_2(D_361,A_362,k2_zfmisc_1(B_360,C_363))
      | ~ v1_funct_1(D_361)
      | v1_xboole_0(C_363)
      | v1_xboole_0(B_360)
      | v1_xboole_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_16,c_310])).

tff(c_357,plain,(
    ! [F_364] :
      ( k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_364)) = k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_364)
      | ~ m1_subset_1(F_364,'#skF_3')
      | ~ v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
      | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130,c_355])).

tff(c_360,plain,(
    ! [F_364] :
      ( k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_364)) = k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_364)
      | ~ m1_subset_1(F_364,'#skF_3')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_116,c_357])).

tff(c_362,plain,(
    ! [F_365] :
      ( k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_365)) = k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_365)
      | ~ m1_subset_1(F_365,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_360])).

tff(c_101,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( v1_funct_1(k5_funct_2(A_251,B_252,C_253,D_254))
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(A_251,k2_zfmisc_1(B_252,C_253))))
      | ~ v1_funct_2(D_254,A_251,k2_zfmisc_1(B_252,C_253))
      | ~ v1_funct_1(D_254)
      | v1_xboole_0(C_253)
      | v1_xboole_0(B_252)
      | v1_xboole_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_104,plain,
    ( v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_107,plain,
    ( v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_104])).

tff(c_108,plain,(
    v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_107])).

tff(c_117,plain,(
    ! [A_259,B_260,C_261,D_262] :
      ( v1_funct_2(k5_funct_2(A_259,B_260,C_261,D_262),A_259,C_261)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(A_259,k2_zfmisc_1(B_260,C_261))))
      | ~ v1_funct_2(D_262,A_259,k2_zfmisc_1(B_260,C_261))
      | ~ v1_funct_1(D_262)
      | v1_xboole_0(C_261)
      | v1_xboole_0(B_260)
      | v1_xboole_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_119,plain,
    ( v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_117])).

tff(c_122,plain,
    ( v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_119])).

tff(c_123,plain,(
    v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_122])).

tff(c_22,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( m1_subset_1(k5_funct_2(A_197,B_198,C_199,D_200),k1_zfmisc_1(k2_zfmisc_1(A_197,C_199)))
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_197,k2_zfmisc_1(B_198,C_199))))
      | ~ v1_funct_2(D_200,A_197,k2_zfmisc_1(B_198,C_199))
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(C_199)
      | v1_xboole_0(B_198)
      | v1_xboole_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_306,plain,(
    ! [D_346,B_344,C_343,F_342,A_345] :
      ( k3_funct_2(A_345,C_343,k5_funct_2(A_345,B_344,C_343,D_346),F_342) = k2_mcart_1(k3_funct_2(A_345,k2_zfmisc_1(B_344,C_343),D_346,F_342))
      | ~ m1_subset_1(F_342,A_345)
      | ~ m1_subset_1(k5_funct_2(A_345,B_344,C_343,D_346),k1_zfmisc_1(k2_zfmisc_1(A_345,C_343)))
      | ~ v1_funct_2(k5_funct_2(A_345,B_344,C_343,D_346),A_345,C_343)
      | ~ v1_funct_1(k5_funct_2(A_345,B_344,C_343,D_346))
      | ~ m1_subset_1(D_346,k1_zfmisc_1(k2_zfmisc_1(A_345,k2_zfmisc_1(B_344,C_343))))
      | ~ v1_funct_2(D_346,A_345,k2_zfmisc_1(B_344,C_343))
      | ~ v1_funct_1(D_346)
      | v1_xboole_0(C_343)
      | v1_xboole_0(B_344)
      | v1_xboole_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_314,plain,(
    ! [C_353,F_355,D_354,B_352,A_356] :
      ( k3_funct_2(A_356,C_353,k5_funct_2(A_356,B_352,C_353,D_354),F_355) = k2_mcart_1(k3_funct_2(A_356,k2_zfmisc_1(B_352,C_353),D_354,F_355))
      | ~ m1_subset_1(F_355,A_356)
      | ~ v1_funct_2(k5_funct_2(A_356,B_352,C_353,D_354),A_356,C_353)
      | ~ v1_funct_1(k5_funct_2(A_356,B_352,C_353,D_354))
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_zfmisc_1(A_356,k2_zfmisc_1(B_352,C_353))))
      | ~ v1_funct_2(D_354,A_356,k2_zfmisc_1(B_352,C_353))
      | ~ v1_funct_1(D_354)
      | v1_xboole_0(C_353)
      | v1_xboole_0(B_352)
      | v1_xboole_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_22,c_306])).

tff(c_316,plain,(
    ! [F_355] :
      ( k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_355)) = k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_355)
      | ~ m1_subset_1(F_355,'#skF_3')
      | ~ v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
      | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_123,c_314])).

tff(c_319,plain,(
    ! [F_355] :
      ( k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_355)) = k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_355)
      | ~ m1_subset_1(F_355,'#skF_3')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_108,c_316])).

tff(c_321,plain,(
    ! [F_357] :
      ( k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_357)) = k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_357)
      | ~ m1_subset_1(F_357,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_319])).

tff(c_30,plain,(
    ! [A_203,B_204] : v1_relat_1(k2_zfmisc_1(A_203,B_204)) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_68,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( m1_subset_1(k3_funct_2(A_245,B_246,C_247,D_248),B_246)
      | ~ m1_subset_1(D_248,A_245)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ v1_funct_2(C_247,A_245,B_246)
      | ~ v1_funct_1(C_247)
      | v1_xboole_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_70,plain,(
    ! [D_248] :
      ( m1_subset_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_248),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_248,'#skF_3')
      | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_73,plain,(
    ! [D_248] :
      ( m1_subset_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_248),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_248,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_70])).

tff(c_75,plain,(
    ! [D_249] :
      ( m1_subset_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_249,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_73])).

tff(c_34,plain,(
    ! [A_207,B_208] :
      ( r2_hidden(A_207,B_208)
      | v1_xboole_0(B_208)
      | ~ m1_subset_1(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    ! [A_241,B_242] :
      ( k4_tarski(k1_mcart_1(A_241),k2_mcart_1(A_241)) = A_241
      | ~ r2_hidden(A_241,B_242)
      | ~ v1_relat_1(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_57,plain,(
    ! [A_207,B_208] :
      ( k4_tarski(k1_mcart_1(A_207),k2_mcart_1(A_207)) = A_207
      | ~ v1_relat_1(B_208)
      | v1_xboole_0(B_208)
      | ~ m1_subset_1(A_207,B_208) ) ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_77,plain,(
    ! [D_249] :
      ( k4_tarski(k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249)),k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249))) = k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5'))
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_249,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_75,c_57])).

tff(c_80,plain,(
    ! [D_249] :
      ( k4_tarski(k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249)),k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249))) = k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249)
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_249,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_82,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_28,plain,(
    ! [A_201,B_202] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_201,B_202))
      | v1_xboole_0(B_202)
      | v1_xboole_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_85,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_28])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_85])).

tff(c_90,plain,(
    ! [D_249] :
      ( k4_tarski(k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249)),k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249))) = k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',D_249)
      | ~ m1_subset_1(D_249,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_330,plain,(
    ! [F_357] :
      ( k4_tarski(k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_357)),k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_357)) = k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_357)
      | ~ m1_subset_1(F_357,'#skF_3')
      | ~ m1_subset_1(F_357,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_90])).

tff(c_395,plain,(
    ! [F_367] :
      ( k4_tarski(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_367),k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_367)) = k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_367)
      | ~ m1_subset_1(F_367,'#skF_3')
      | ~ m1_subset_1(F_367,'#skF_3')
      | ~ m1_subset_1(F_367,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_330])).

tff(c_36,plain,(
    k4_tarski(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7'),k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')) != k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_401,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_36])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_401])).

%------------------------------------------------------------------------------
