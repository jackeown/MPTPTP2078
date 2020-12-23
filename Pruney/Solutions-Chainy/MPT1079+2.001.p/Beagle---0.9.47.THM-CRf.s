%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  136 (1006 expanded)
%              Number of leaves         :   38 ( 406 expanded)
%              Depth                    :   17
%              Number of atoms          :  418 (4519 expanded)
%              Number of equality atoms :   50 ( 441 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_funct_2 > k4_funct_2 > k3_funct_2 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_210,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_funct_2)).

tff(f_154,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C))))
     => v1_relat_1(k2_relat_1(D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_186,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,B)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_funct_2)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_funct_2)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_funct_2)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_funct_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_54,plain,(
    ! [D_255,A_256,B_257,C_258] :
      ( v1_relat_1(k2_relat_1(D_255))
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_256,k2_zfmisc_1(B_257,C_258)))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v1_relat_1(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_40,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_60,plain,(
    ! [A_261,B_262,C_263] :
      ( k2_relset_1(A_261,B_262,C_263) = k2_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    k2_relset_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_69,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k3_funct_2(A_264,B_265,C_266,D_267) = k1_funct_1(C_266,D_267)
      | ~ m1_subset_1(D_267,A_264)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265)))
      | ~ v1_funct_2(C_266,A_264,B_265)
      | ~ v1_funct_1(C_266)
      | v1_xboole_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_73,plain,(
    ! [B_265,C_266] :
      ( k3_funct_2('#skF_3',B_265,C_266,'#skF_7') = k1_funct_1(C_266,'#skF_7')
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_265)))
      | ~ v1_funct_2(C_266,'#skF_3',B_265)
      | ~ v1_funct_1(C_266)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_86,plain,(
    ! [B_272,C_273] :
      ( k3_funct_2('#skF_3',B_272,C_273,'#skF_7') = k1_funct_1(C_273,'#skF_7')
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_272)))
      | ~ v1_funct_2(C_273,'#skF_3',B_272)
      | ~ v1_funct_1(C_273) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_73])).

tff(c_89,plain,
    ( k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_92,plain,(
    k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_89])).

tff(c_106,plain,(
    ! [A_278,B_279,D_280,C_281] :
      ( r2_hidden(k3_funct_2(A_278,B_279,D_280,C_281),k2_relset_1(A_278,B_279,D_280))
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_2(D_280,A_278,B_279)
      | ~ v1_funct_1(D_280)
      | ~ m1_subset_1(C_281,A_278)
      | v1_xboole_0(B_279)
      | v1_xboole_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_111,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),k2_relset_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3')
    | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_106])).

tff(c_117,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),k2_relat_1('#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_46,c_44,c_42,c_64,c_111])).

tff(c_118,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),k2_relat_1('#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_117])).

tff(c_122,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_1,B_2))
      | v1_xboole_0(B_2)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_125])).

tff(c_130,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k4_tarski(k1_mcart_1(A_6),k2_mcart_1(A_6)) = A_6
      | ~ r2_hidden(A_6,B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,
    ( k4_tarski(k1_mcart_1(k1_funct_1('#skF_6','#skF_7')),k2_mcart_1(k1_funct_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_relat_1(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_130,c_6])).

tff(c_143,plain,(
    k4_tarski(k1_mcart_1(k1_funct_1('#skF_6','#skF_7')),k2_mcart_1(k1_funct_1('#skF_6','#skF_7'))) = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_140])).

tff(c_78,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( v1_funct_1(k4_funct_2(A_268,B_269,C_270,D_271))
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1(A_268,k2_zfmisc_1(B_269,C_270))))
      | ~ v1_funct_2(D_271,A_268,k2_zfmisc_1(B_269,C_270))
      | ~ v1_funct_1(D_271)
      | v1_xboole_0(C_270)
      | v1_xboole_0(B_269)
      | v1_xboole_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_81,plain,
    ( v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_78])).

tff(c_84,plain,
    ( v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_81])).

tff(c_85,plain,(
    v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_84])).

tff(c_179,plain,(
    ! [A_288,B_289,C_290,D_291] :
      ( v1_funct_2(k4_funct_2(A_288,B_289,C_290,D_291),A_288,B_289)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(A_288,k2_zfmisc_1(B_289,C_290))))
      | ~ v1_funct_2(D_291,A_288,k2_zfmisc_1(B_289,C_290))
      | ~ v1_funct_1(D_291)
      | v1_xboole_0(C_290)
      | v1_xboole_0(B_289)
      | v1_xboole_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_181,plain,
    ( v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_179])).

tff(c_184,plain,
    ( v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_181])).

tff(c_185,plain,(
    v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_184])).

tff(c_20,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( m1_subset_1(k4_funct_2(A_196,B_197,C_198,D_199),k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(A_196,k2_zfmisc_1(B_197,C_198))))
      | ~ v1_funct_2(D_199,A_196,k2_zfmisc_1(B_197,C_198))
      | ~ v1_funct_1(D_199)
      | v1_xboole_0(C_198)
      | v1_xboole_0(B_197)
      | v1_xboole_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_186,plain,(
    ! [A_292,B_293,C_294,D_295] :
      ( m1_subset_1(k4_funct_2(A_292,B_293,C_294,D_295),k1_zfmisc_1(k2_zfmisc_1(A_292,B_293)))
      | ~ m1_subset_1(D_295,k1_zfmisc_1(k2_zfmisc_1(A_292,k2_zfmisc_1(B_293,C_294))))
      | ~ v1_funct_2(D_295,A_292,k2_zfmisc_1(B_293,C_294))
      | ~ v1_funct_1(D_295)
      | v1_xboole_0(C_294)
      | v1_xboole_0(B_293)
      | v1_xboole_0(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( k2_relset_1(A_3,B_4,C_5) = k2_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_262,plain,(
    ! [A_300,B_301,C_302,D_303] :
      ( k2_relset_1(A_300,B_301,k4_funct_2(A_300,B_301,C_302,D_303)) = k2_relat_1(k4_funct_2(A_300,B_301,C_302,D_303))
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(A_300,k2_zfmisc_1(B_301,C_302))))
      | ~ v1_funct_2(D_303,A_300,k2_zfmisc_1(B_301,C_302))
      | ~ v1_funct_1(D_303)
      | v1_xboole_0(C_302)
      | v1_xboole_0(B_301)
      | v1_xboole_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_186,c_4])).

tff(c_270,plain,
    ( k2_relset_1('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) = k2_relat_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_262])).

tff(c_275,plain,
    ( k2_relset_1('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) = k2_relat_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_270])).

tff(c_276,plain,(
    k2_relset_1('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) = k2_relat_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_275])).

tff(c_36,plain,(
    ! [A_212,B_220,D_226,C_224] :
      ( r2_hidden(k3_funct_2(A_212,B_220,D_226,C_224),k2_relset_1(A_212,B_220,D_226))
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1(A_212,B_220)))
      | ~ v1_funct_2(D_226,A_212,B_220)
      | ~ v1_funct_1(D_226)
      | ~ m1_subset_1(C_224,A_212)
      | v1_xboole_0(B_220)
      | v1_xboole_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_280,plain,(
    ! [C_224] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),C_224),k2_relat_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_subset_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
      | ~ v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(C_224,'#skF_3')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_36])).

tff(c_284,plain,(
    ! [C_224] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),C_224),k2_relat_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_subset_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(C_224,'#skF_3')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_185,c_280])).

tff(c_285,plain,(
    ! [C_224] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),C_224),k2_relat_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_subset_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(C_224,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_284])).

tff(c_287,plain,(
    ~ m1_subset_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_291,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_287])).

tff(c_294,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_291])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_294])).

tff(c_298,plain,(
    m1_subset_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_77,plain,(
    ! [B_265,C_266] :
      ( k3_funct_2('#skF_3',B_265,C_266,'#skF_7') = k1_funct_1(C_266,'#skF_7')
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_265)))
      | ~ v1_funct_2(C_266,'#skF_3',B_265)
      | ~ v1_funct_1(C_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_73])).

tff(c_301,plain,
    ( k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')
    | ~ v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
    | ~ v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_298,c_77])).

tff(c_309,plain,(
    k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_185,c_301])).

tff(c_781,plain,(
    ! [C_382,A_383,B_381,F_384,D_385] :
      ( k3_funct_2(A_383,B_381,k4_funct_2(A_383,B_381,C_382,D_385),F_384) = k1_mcart_1(k3_funct_2(A_383,k2_zfmisc_1(B_381,C_382),D_385,F_384))
      | ~ m1_subset_1(F_384,A_383)
      | ~ m1_subset_1(k4_funct_2(A_383,B_381,C_382,D_385),k1_zfmisc_1(k2_zfmisc_1(A_383,B_381)))
      | ~ v1_funct_2(k4_funct_2(A_383,B_381,C_382,D_385),A_383,B_381)
      | ~ v1_funct_1(k4_funct_2(A_383,B_381,C_382,D_385))
      | ~ m1_subset_1(D_385,k1_zfmisc_1(k2_zfmisc_1(A_383,k2_zfmisc_1(B_381,C_382))))
      | ~ v1_funct_2(D_385,A_383,k2_zfmisc_1(B_381,C_382))
      | ~ v1_funct_1(D_385)
      | v1_xboole_0(C_382)
      | v1_xboole_0(B_381)
      | v1_xboole_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_783,plain,(
    ! [F_384] :
      ( k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_384)) = k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_384)
      | ~ m1_subset_1(F_384,'#skF_3')
      | ~ v1_funct_2(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_4')
      | ~ v1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
      | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_298,c_781])).

tff(c_788,plain,(
    ! [F_384] :
      ( k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_384)) = k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_384)
      | ~ m1_subset_1(F_384,'#skF_3')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_85,c_185,c_783])).

tff(c_791,plain,(
    ! [F_386] :
      ( k1_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_386)) = k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_386)
      | ~ m1_subset_1(F_386,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_788])).

tff(c_812,plain,
    ( k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_mcart_1(k1_funct_1('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_791])).

tff(c_822,plain,(
    k1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_mcart_1(k1_funct_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_309,c_812])).

tff(c_98,plain,(
    ! [A_274,B_275,C_276,D_277] :
      ( v1_funct_1(k5_funct_2(A_274,B_275,C_276,D_277))
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_274,k2_zfmisc_1(B_275,C_276))))
      | ~ v1_funct_2(D_277,A_274,k2_zfmisc_1(B_275,C_276))
      | ~ v1_funct_1(D_277)
      | v1_xboole_0(C_276)
      | v1_xboole_0(B_275)
      | v1_xboole_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_101,plain,
    ( v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_104,plain,
    ( v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_101])).

tff(c_105,plain,(
    v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_104])).

tff(c_132,plain,(
    ! [A_282,B_283,C_284,D_285] :
      ( v1_funct_2(k5_funct_2(A_282,B_283,C_284,D_285),A_282,C_284)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1(A_282,k2_zfmisc_1(B_283,C_284))))
      | ~ v1_funct_2(D_285,A_282,k2_zfmisc_1(B_283,C_284))
      | ~ v1_funct_1(D_285)
      | v1_xboole_0(C_284)
      | v1_xboole_0(B_283)
      | v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_134,plain,
    ( v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_132])).

tff(c_137,plain,
    ( v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_134])).

tff(c_138,plain,(
    v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_137])).

tff(c_26,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( m1_subset_1(k5_funct_2(A_200,B_201,C_202,D_203),k1_zfmisc_1(k2_zfmisc_1(A_200,C_202)))
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(A_200,k2_zfmisc_1(B_201,C_202))))
      | ~ v1_funct_2(D_203,A_200,k2_zfmisc_1(B_201,C_202))
      | ~ v1_funct_1(D_203)
      | v1_xboole_0(C_202)
      | v1_xboole_0(B_201)
      | v1_xboole_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_224,plain,(
    ! [A_296,B_297,C_298,D_299] :
      ( m1_subset_1(k5_funct_2(A_296,B_297,C_298,D_299),k1_zfmisc_1(k2_zfmisc_1(A_296,C_298)))
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1(A_296,k2_zfmisc_1(B_297,C_298))))
      | ~ v1_funct_2(D_299,A_296,k2_zfmisc_1(B_297,C_298))
      | ~ v1_funct_1(D_299)
      | v1_xboole_0(C_298)
      | v1_xboole_0(B_297)
      | v1_xboole_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_371,plain,(
    ! [A_312,C_313,B_314,D_315] :
      ( k2_relset_1(A_312,C_313,k5_funct_2(A_312,B_314,C_313,D_315)) = k2_relat_1(k5_funct_2(A_312,B_314,C_313,D_315))
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_312,k2_zfmisc_1(B_314,C_313))))
      | ~ v1_funct_2(D_315,A_312,k2_zfmisc_1(B_314,C_313))
      | ~ v1_funct_1(D_315)
      | v1_xboole_0(C_313)
      | v1_xboole_0(B_314)
      | v1_xboole_0(A_312) ) ),
    inference(resolution,[status(thm)],[c_224,c_4])).

tff(c_379,plain,
    ( k2_relset_1('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) = k2_relat_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_371])).

tff(c_384,plain,
    ( k2_relset_1('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) = k2_relat_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_379])).

tff(c_385,plain,(
    k2_relset_1('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) = k2_relat_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_384])).

tff(c_389,plain,(
    ! [C_224] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),C_224),k2_relat_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_subset_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
      | ~ v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
      | ~ v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(C_224,'#skF_3')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_36])).

tff(c_393,plain,(
    ! [C_224] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),C_224),k2_relat_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_subset_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
      | ~ m1_subset_1(C_224,'#skF_3')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_138,c_389])).

tff(c_394,plain,(
    ! [C_224] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),C_224),k2_relat_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_subset_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
      | ~ m1_subset_1(C_224,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_393])).

tff(c_396,plain,(
    ~ m1_subset_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_399,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
    | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_396])).

tff(c_402,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_399])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_402])).

tff(c_406,plain,(
    m1_subset_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_432,plain,
    ( k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')
    | ~ v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
    | ~ v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_406,c_77])).

tff(c_448,plain,(
    k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_138,c_432])).

tff(c_678,plain,(
    ! [F_373,D_374,C_377,A_376,B_375] :
      ( k3_funct_2(A_376,C_377,k5_funct_2(A_376,B_375,C_377,D_374),F_373) = k2_mcart_1(k3_funct_2(A_376,k2_zfmisc_1(B_375,C_377),D_374,F_373))
      | ~ m1_subset_1(F_373,A_376)
      | ~ m1_subset_1(k5_funct_2(A_376,B_375,C_377,D_374),k1_zfmisc_1(k2_zfmisc_1(A_376,C_377)))
      | ~ v1_funct_2(k5_funct_2(A_376,B_375,C_377,D_374),A_376,C_377)
      | ~ v1_funct_1(k5_funct_2(A_376,B_375,C_377,D_374))
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(A_376,k2_zfmisc_1(B_375,C_377))))
      | ~ v1_funct_2(D_374,A_376,k2_zfmisc_1(B_375,C_377))
      | ~ v1_funct_1(D_374)
      | v1_xboole_0(C_377)
      | v1_xboole_0(B_375)
      | v1_xboole_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_680,plain,(
    ! [F_373] :
      ( k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_373)) = k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_373)
      | ~ m1_subset_1(F_373,'#skF_3')
      | ~ v1_funct_2(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3','#skF_5')
      | ~ v1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))))
      | ~ v1_funct_2('#skF_6','#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_406,c_678])).

tff(c_685,plain,(
    ! [F_373] :
      ( k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_373)) = k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_373)
      | ~ m1_subset_1(F_373,'#skF_3')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_105,c_138,c_680])).

tff(c_688,plain,(
    ! [F_378] :
      ( k2_mcart_1(k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6',F_378)) = k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),F_378)
      | ~ m1_subset_1(F_378,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_685])).

tff(c_706,plain,
    ( k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k2_mcart_1(k1_funct_1('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_688])).

tff(c_716,plain,(
    k1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') = k2_mcart_1(k1_funct_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_448,c_706])).

tff(c_38,plain,(
    k4_tarski(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7'),k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')) != k3_funct_2('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_93,plain,(
    k4_tarski(k3_funct_2('#skF_3','#skF_4',k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7'),k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')) != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38])).

tff(c_313,plain,(
    k4_tarski(k1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7'),k3_funct_2('#skF_3','#skF_5',k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')) != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_93])).

tff(c_452,plain,(
    k4_tarski(k1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7'),k1_funct_1(k5_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')) != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_313])).

tff(c_717,plain,(
    k4_tarski(k1_funct_1(k4_funct_2('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7'),k2_mcart_1(k1_funct_1('#skF_6','#skF_7'))) != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_452])).

tff(c_823,plain,(
    k4_tarski(k1_mcart_1(k1_funct_1('#skF_6','#skF_7')),k2_mcart_1(k1_funct_1('#skF_6','#skF_7'))) != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_717])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.63  
% 3.87/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.64  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_funct_2 > k4_funct_2 > k3_funct_2 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 4.01/1.64  
% 4.01/1.64  %Foreground sorts:
% 4.01/1.64  
% 4.01/1.64  
% 4.01/1.64  %Background operators:
% 4.01/1.64  
% 4.01/1.64  
% 4.01/1.64  %Foreground operators:
% 4.01/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.01/1.64  tff(k4_funct_2, type, k4_funct_2: ($i * $i * $i * $i) > $i).
% 4.01/1.64  tff(k5_funct_2, type, k5_funct_2: ($i * $i * $i * $i) > $i).
% 4.01/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.01/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.01/1.64  tff('#skF_7', type, '#skF_7': $i).
% 4.01/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.64  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.01/1.64  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.64  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.01/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 4.01/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.64  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.01/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.64  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.64  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.01/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.64  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.01/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.64  
% 4.01/1.66  tff(f_210, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k2_zfmisc_1(B, C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k2_zfmisc_1(B, C))))) => (![E]: (m1_subset_1(E, A) => (k3_funct_2(A, k2_zfmisc_1(B, C), D, E) = k4_tarski(k3_funct_2(A, B, k4_funct_2(A, B, C, D), E), k3_funct_2(A, C, k5_funct_2(A, B, C, D), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_funct_2)).
% 4.01/1.66  tff(f_154, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k2_zfmisc_1(B, C)))) => v1_relat_1(k2_relat_1(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relset_1)).
% 4.01/1.66  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.01/1.66  tff(f_167, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.01/1.66  tff(f_186, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 4.01/1.66  tff(f_34, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 4.01/1.66  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 4.01/1.66  tff(f_129, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & v1_funct_1(D)) & v1_funct_2(D, A, k2_zfmisc_1(B, C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k2_zfmisc_1(B, C))))) => ((v1_funct_1(k4_funct_2(A, B, C, D)) & v1_funct_2(k4_funct_2(A, B, C, D), A, B)) & m1_subset_1(k4_funct_2(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_funct_2)).
% 4.01/1.66  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k2_zfmisc_1(B, C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k2_zfmisc_1(B, C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((E = k4_funct_2(A, B, C, D)) <=> (![F]: (m1_subset_1(F, A) => (k3_funct_2(A, B, E, F) = k1_mcart_1(k3_funct_2(A, k2_zfmisc_1(B, C), D, F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_funct_2)).
% 4.01/1.66  tff(f_150, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & v1_funct_1(D)) & v1_funct_2(D, A, k2_zfmisc_1(B, C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k2_zfmisc_1(B, C))))) => ((v1_funct_1(k5_funct_2(A, B, C, D)) & v1_funct_2(k5_funct_2(A, B, C, D), A, C)) & m1_subset_1(k5_funct_2(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_funct_2)).
% 4.01/1.66  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k2_zfmisc_1(B, C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k2_zfmisc_1(B, C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => ((E = k5_funct_2(A, B, C, D)) <=> (![F]: (m1_subset_1(F, A) => (k3_funct_2(A, C, E, F) = k2_mcart_1(k3_funct_2(A, k2_zfmisc_1(B, C), D, F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_funct_2)).
% 4.01/1.66  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_54, plain, (![D_255, A_256, B_257, C_258]: (v1_relat_1(k2_relat_1(D_255)) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_256, k2_zfmisc_1(B_257, C_258)))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.01/1.66  tff(c_58, plain, (v1_relat_1(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_54])).
% 4.01/1.66  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_40, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_60, plain, (![A_261, B_262, C_263]: (k2_relset_1(A_261, B_262, C_263)=k2_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.66  tff(c_64, plain, (k2_relset_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_60])).
% 4.01/1.66  tff(c_69, plain, (![A_264, B_265, C_266, D_267]: (k3_funct_2(A_264, B_265, C_266, D_267)=k1_funct_1(C_266, D_267) | ~m1_subset_1(D_267, A_264) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))) | ~v1_funct_2(C_266, A_264, B_265) | ~v1_funct_1(C_266) | v1_xboole_0(A_264))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.01/1.66  tff(c_73, plain, (![B_265, C_266]: (k3_funct_2('#skF_3', B_265, C_266, '#skF_7')=k1_funct_1(C_266, '#skF_7') | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_265))) | ~v1_funct_2(C_266, '#skF_3', B_265) | ~v1_funct_1(C_266) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_69])).
% 4.01/1.66  tff(c_86, plain, (![B_272, C_273]: (k3_funct_2('#skF_3', B_272, C_273, '#skF_7')=k1_funct_1(C_273, '#skF_7') | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_272))) | ~v1_funct_2(C_273, '#skF_3', B_272) | ~v1_funct_1(C_273))), inference(negUnitSimplification, [status(thm)], [c_52, c_73])).
% 4.01/1.66  tff(c_89, plain, (k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_86])).
% 4.01/1.66  tff(c_92, plain, (k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_89])).
% 4.01/1.66  tff(c_106, plain, (![A_278, B_279, D_280, C_281]: (r2_hidden(k3_funct_2(A_278, B_279, D_280, C_281), k2_relset_1(A_278, B_279, D_280)) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_2(D_280, A_278, B_279) | ~v1_funct_1(D_280) | ~m1_subset_1(C_281, A_278) | v1_xboole_0(B_279) | v1_xboole_0(A_278))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.01/1.66  tff(c_111, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), k2_relset_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3') | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_106])).
% 4.01/1.66  tff(c_117, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), k2_relat_1('#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_46, c_44, c_42, c_64, c_111])).
% 4.01/1.66  tff(c_118, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), k2_relat_1('#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_117])).
% 4.01/1.66  tff(c_122, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_118])).
% 4.01/1.66  tff(c_2, plain, (![A_1, B_2]: (~v1_xboole_0(k2_zfmisc_1(A_1, B_2)) | v1_xboole_0(B_2) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.01/1.66  tff(c_125, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_122, c_2])).
% 4.01/1.66  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_125])).
% 4.01/1.66  tff(c_130, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_118])).
% 4.01/1.66  tff(c_6, plain, (![A_6, B_7]: (k4_tarski(k1_mcart_1(A_6), k2_mcart_1(A_6))=A_6 | ~r2_hidden(A_6, B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.01/1.66  tff(c_140, plain, (k4_tarski(k1_mcart_1(k1_funct_1('#skF_6', '#skF_7')), k2_mcart_1(k1_funct_1('#skF_6', '#skF_7')))=k1_funct_1('#skF_6', '#skF_7') | ~v1_relat_1(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_130, c_6])).
% 4.01/1.66  tff(c_143, plain, (k4_tarski(k1_mcart_1(k1_funct_1('#skF_6', '#skF_7')), k2_mcart_1(k1_funct_1('#skF_6', '#skF_7')))=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_140])).
% 4.01/1.66  tff(c_78, plain, (![A_268, B_269, C_270, D_271]: (v1_funct_1(k4_funct_2(A_268, B_269, C_270, D_271)) | ~m1_subset_1(D_271, k1_zfmisc_1(k2_zfmisc_1(A_268, k2_zfmisc_1(B_269, C_270)))) | ~v1_funct_2(D_271, A_268, k2_zfmisc_1(B_269, C_270)) | ~v1_funct_1(D_271) | v1_xboole_0(C_270) | v1_xboole_0(B_269) | v1_xboole_0(A_268))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.01/1.66  tff(c_81, plain, (v1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_78])).
% 4.01/1.66  tff(c_84, plain, (v1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_81])).
% 4.01/1.66  tff(c_85, plain, (v1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_84])).
% 4.01/1.66  tff(c_179, plain, (![A_288, B_289, C_290, D_291]: (v1_funct_2(k4_funct_2(A_288, B_289, C_290, D_291), A_288, B_289) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(A_288, k2_zfmisc_1(B_289, C_290)))) | ~v1_funct_2(D_291, A_288, k2_zfmisc_1(B_289, C_290)) | ~v1_funct_1(D_291) | v1_xboole_0(C_290) | v1_xboole_0(B_289) | v1_xboole_0(A_288))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.01/1.66  tff(c_181, plain, (v1_funct_2(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_179])).
% 4.01/1.66  tff(c_184, plain, (v1_funct_2(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_181])).
% 4.01/1.66  tff(c_185, plain, (v1_funct_2(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_184])).
% 4.01/1.66  tff(c_20, plain, (![A_196, B_197, C_198, D_199]: (m1_subset_1(k4_funct_2(A_196, B_197, C_198, D_199), k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(A_196, k2_zfmisc_1(B_197, C_198)))) | ~v1_funct_2(D_199, A_196, k2_zfmisc_1(B_197, C_198)) | ~v1_funct_1(D_199) | v1_xboole_0(C_198) | v1_xboole_0(B_197) | v1_xboole_0(A_196))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.01/1.66  tff(c_186, plain, (![A_292, B_293, C_294, D_295]: (m1_subset_1(k4_funct_2(A_292, B_293, C_294, D_295), k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))) | ~m1_subset_1(D_295, k1_zfmisc_1(k2_zfmisc_1(A_292, k2_zfmisc_1(B_293, C_294)))) | ~v1_funct_2(D_295, A_292, k2_zfmisc_1(B_293, C_294)) | ~v1_funct_1(D_295) | v1_xboole_0(C_294) | v1_xboole_0(B_293) | v1_xboole_0(A_292))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.01/1.66  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_relset_1(A_3, B_4, C_5)=k2_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.66  tff(c_262, plain, (![A_300, B_301, C_302, D_303]: (k2_relset_1(A_300, B_301, k4_funct_2(A_300, B_301, C_302, D_303))=k2_relat_1(k4_funct_2(A_300, B_301, C_302, D_303)) | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(A_300, k2_zfmisc_1(B_301, C_302)))) | ~v1_funct_2(D_303, A_300, k2_zfmisc_1(B_301, C_302)) | ~v1_funct_1(D_303) | v1_xboole_0(C_302) | v1_xboole_0(B_301) | v1_xboole_0(A_300))), inference(resolution, [status(thm)], [c_186, c_4])).
% 4.01/1.66  tff(c_270, plain, (k2_relset_1('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k2_relat_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_262])).
% 4.01/1.66  tff(c_275, plain, (k2_relset_1('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k2_relat_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_270])).
% 4.01/1.66  tff(c_276, plain, (k2_relset_1('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k2_relat_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_275])).
% 4.01/1.66  tff(c_36, plain, (![A_212, B_220, D_226, C_224]: (r2_hidden(k3_funct_2(A_212, B_220, D_226, C_224), k2_relset_1(A_212, B_220, D_226)) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1(A_212, B_220))) | ~v1_funct_2(D_226, A_212, B_220) | ~v1_funct_1(D_226) | ~m1_subset_1(C_224, A_212) | v1_xboole_0(B_220) | v1_xboole_0(A_212))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.01/1.66  tff(c_280, plain, (![C_224]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), C_224), k2_relat_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | ~v1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(C_224, '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_36])).
% 4.01/1.66  tff(c_284, plain, (![C_224]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), C_224), k2_relat_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~m1_subset_1(C_224, '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_185, c_280])).
% 4.01/1.66  tff(c_285, plain, (![C_224]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), C_224), k2_relat_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~m1_subset_1(C_224, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_284])).
% 4.01/1.66  tff(c_287, plain, (~m1_subset_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_285])).
% 4.01/1.66  tff(c_291, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_287])).
% 4.01/1.66  tff(c_294, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_291])).
% 4.01/1.66  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_294])).
% 4.01/1.66  tff(c_298, plain, (m1_subset_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_285])).
% 4.01/1.66  tff(c_77, plain, (![B_265, C_266]: (k3_funct_2('#skF_3', B_265, C_266, '#skF_7')=k1_funct_1(C_266, '#skF_7') | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_265))) | ~v1_funct_2(C_266, '#skF_3', B_265) | ~v1_funct_1(C_266))), inference(negUnitSimplification, [status(thm)], [c_52, c_73])).
% 4.01/1.66  tff(c_301, plain, (k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7') | ~v1_funct_2(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | ~v1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_298, c_77])).
% 4.01/1.66  tff(c_309, plain, (k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_185, c_301])).
% 4.01/1.66  tff(c_781, plain, (![C_382, A_383, B_381, F_384, D_385]: (k3_funct_2(A_383, B_381, k4_funct_2(A_383, B_381, C_382, D_385), F_384)=k1_mcart_1(k3_funct_2(A_383, k2_zfmisc_1(B_381, C_382), D_385, F_384)) | ~m1_subset_1(F_384, A_383) | ~m1_subset_1(k4_funct_2(A_383, B_381, C_382, D_385), k1_zfmisc_1(k2_zfmisc_1(A_383, B_381))) | ~v1_funct_2(k4_funct_2(A_383, B_381, C_382, D_385), A_383, B_381) | ~v1_funct_1(k4_funct_2(A_383, B_381, C_382, D_385)) | ~m1_subset_1(D_385, k1_zfmisc_1(k2_zfmisc_1(A_383, k2_zfmisc_1(B_381, C_382)))) | ~v1_funct_2(D_385, A_383, k2_zfmisc_1(B_381, C_382)) | ~v1_funct_1(D_385) | v1_xboole_0(C_382) | v1_xboole_0(B_381) | v1_xboole_0(A_383))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.66  tff(c_783, plain, (![F_384]: (k1_mcart_1(k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', F_384))=k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), F_384) | ~m1_subset_1(F_384, '#skF_3') | ~v1_funct_2(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | ~v1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_298, c_781])).
% 4.01/1.66  tff(c_788, plain, (![F_384]: (k1_mcart_1(k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', F_384))=k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), F_384) | ~m1_subset_1(F_384, '#skF_3') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_85, c_185, c_783])).
% 4.01/1.66  tff(c_791, plain, (![F_386]: (k1_mcart_1(k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', F_386))=k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), F_386) | ~m1_subset_1(F_386, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_788])).
% 4.01/1.66  tff(c_812, plain, (k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_mcart_1(k1_funct_1('#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_791])).
% 4.01/1.66  tff(c_822, plain, (k1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_mcart_1(k1_funct_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_309, c_812])).
% 4.01/1.66  tff(c_98, plain, (![A_274, B_275, C_276, D_277]: (v1_funct_1(k5_funct_2(A_274, B_275, C_276, D_277)) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_274, k2_zfmisc_1(B_275, C_276)))) | ~v1_funct_2(D_277, A_274, k2_zfmisc_1(B_275, C_276)) | ~v1_funct_1(D_277) | v1_xboole_0(C_276) | v1_xboole_0(B_275) | v1_xboole_0(A_274))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.66  tff(c_101, plain, (v1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_98])).
% 4.01/1.66  tff(c_104, plain, (v1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_101])).
% 4.01/1.66  tff(c_105, plain, (v1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_104])).
% 4.01/1.66  tff(c_132, plain, (![A_282, B_283, C_284, D_285]: (v1_funct_2(k5_funct_2(A_282, B_283, C_284, D_285), A_282, C_284) | ~m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1(A_282, k2_zfmisc_1(B_283, C_284)))) | ~v1_funct_2(D_285, A_282, k2_zfmisc_1(B_283, C_284)) | ~v1_funct_1(D_285) | v1_xboole_0(C_284) | v1_xboole_0(B_283) | v1_xboole_0(A_282))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.66  tff(c_134, plain, (v1_funct_2(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_132])).
% 4.01/1.66  tff(c_137, plain, (v1_funct_2(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_134])).
% 4.01/1.66  tff(c_138, plain, (v1_funct_2(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_137])).
% 4.01/1.66  tff(c_26, plain, (![A_200, B_201, C_202, D_203]: (m1_subset_1(k5_funct_2(A_200, B_201, C_202, D_203), k1_zfmisc_1(k2_zfmisc_1(A_200, C_202))) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(A_200, k2_zfmisc_1(B_201, C_202)))) | ~v1_funct_2(D_203, A_200, k2_zfmisc_1(B_201, C_202)) | ~v1_funct_1(D_203) | v1_xboole_0(C_202) | v1_xboole_0(B_201) | v1_xboole_0(A_200))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.66  tff(c_224, plain, (![A_296, B_297, C_298, D_299]: (m1_subset_1(k5_funct_2(A_296, B_297, C_298, D_299), k1_zfmisc_1(k2_zfmisc_1(A_296, C_298))) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1(A_296, k2_zfmisc_1(B_297, C_298)))) | ~v1_funct_2(D_299, A_296, k2_zfmisc_1(B_297, C_298)) | ~v1_funct_1(D_299) | v1_xboole_0(C_298) | v1_xboole_0(B_297) | v1_xboole_0(A_296))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.66  tff(c_371, plain, (![A_312, C_313, B_314, D_315]: (k2_relset_1(A_312, C_313, k5_funct_2(A_312, B_314, C_313, D_315))=k2_relat_1(k5_funct_2(A_312, B_314, C_313, D_315)) | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_312, k2_zfmisc_1(B_314, C_313)))) | ~v1_funct_2(D_315, A_312, k2_zfmisc_1(B_314, C_313)) | ~v1_funct_1(D_315) | v1_xboole_0(C_313) | v1_xboole_0(B_314) | v1_xboole_0(A_312))), inference(resolution, [status(thm)], [c_224, c_4])).
% 4.01/1.66  tff(c_379, plain, (k2_relset_1('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k2_relat_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_371])).
% 4.01/1.66  tff(c_384, plain, (k2_relset_1('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k2_relat_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_379])).
% 4.01/1.66  tff(c_385, plain, (k2_relset_1('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k2_relat_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_384])).
% 4.01/1.66  tff(c_389, plain, (![C_224]: (r2_hidden(k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), C_224), k2_relat_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_5') | ~v1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(C_224, '#skF_3') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_385, c_36])).
% 4.01/1.66  tff(c_393, plain, (![C_224]: (r2_hidden(k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), C_224), k2_relat_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~m1_subset_1(C_224, '#skF_3') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_138, c_389])).
% 4.01/1.66  tff(c_394, plain, (![C_224]: (r2_hidden(k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), C_224), k2_relat_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~m1_subset_1(C_224, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_393])).
% 4.01/1.66  tff(c_396, plain, (~m1_subset_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitLeft, [status(thm)], [c_394])).
% 4.01/1.66  tff(c_399, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_396])).
% 4.01/1.66  tff(c_402, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_399])).
% 4.01/1.66  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_402])).
% 4.01/1.66  tff(c_406, plain, (m1_subset_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_394])).
% 4.01/1.66  tff(c_432, plain, (k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7') | ~v1_funct_2(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_5') | ~v1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_406, c_77])).
% 4.01/1.66  tff(c_448, plain, (k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_138, c_432])).
% 4.01/1.66  tff(c_678, plain, (![F_373, D_374, C_377, A_376, B_375]: (k3_funct_2(A_376, C_377, k5_funct_2(A_376, B_375, C_377, D_374), F_373)=k2_mcart_1(k3_funct_2(A_376, k2_zfmisc_1(B_375, C_377), D_374, F_373)) | ~m1_subset_1(F_373, A_376) | ~m1_subset_1(k5_funct_2(A_376, B_375, C_377, D_374), k1_zfmisc_1(k2_zfmisc_1(A_376, C_377))) | ~v1_funct_2(k5_funct_2(A_376, B_375, C_377, D_374), A_376, C_377) | ~v1_funct_1(k5_funct_2(A_376, B_375, C_377, D_374)) | ~m1_subset_1(D_374, k1_zfmisc_1(k2_zfmisc_1(A_376, k2_zfmisc_1(B_375, C_377)))) | ~v1_funct_2(D_374, A_376, k2_zfmisc_1(B_375, C_377)) | ~v1_funct_1(D_374) | v1_xboole_0(C_377) | v1_xboole_0(B_375) | v1_xboole_0(A_376))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.01/1.66  tff(c_680, plain, (![F_373]: (k2_mcart_1(k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', F_373))=k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), F_373) | ~m1_subset_1(F_373, '#skF_3') | ~v1_funct_2(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3', '#skF_5') | ~v1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_406, c_678])).
% 4.01/1.66  tff(c_685, plain, (![F_373]: (k2_mcart_1(k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', F_373))=k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), F_373) | ~m1_subset_1(F_373, '#skF_3') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_105, c_138, c_680])).
% 4.01/1.66  tff(c_688, plain, (![F_378]: (k2_mcart_1(k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', F_378))=k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), F_378) | ~m1_subset_1(F_378, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_685])).
% 4.01/1.66  tff(c_706, plain, (k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k2_mcart_1(k1_funct_1('#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_688])).
% 4.01/1.66  tff(c_716, plain, (k1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k2_mcart_1(k1_funct_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_448, c_706])).
% 4.01/1.66  tff(c_38, plain, (k4_tarski(k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'))!=k3_funct_2('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_210])).
% 4.01/1.66  tff(c_93, plain, (k4_tarski(k3_funct_2('#skF_3', '#skF_4', k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'))!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38])).
% 4.01/1.66  tff(c_313, plain, (k4_tarski(k1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k3_funct_2('#skF_3', '#skF_5', k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'))!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_93])).
% 4.01/1.66  tff(c_452, plain, (k4_tarski(k1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k1_funct_1(k5_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'))!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_313])).
% 4.01/1.66  tff(c_717, plain, (k4_tarski(k1_funct_1(k4_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k2_mcart_1(k1_funct_1('#skF_6', '#skF_7')))!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_452])).
% 4.01/1.66  tff(c_823, plain, (k4_tarski(k1_mcart_1(k1_funct_1('#skF_6', '#skF_7')), k2_mcart_1(k1_funct_1('#skF_6', '#skF_7')))!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_822, c_717])).
% 4.01/1.66  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_823])).
% 4.01/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.66  
% 4.01/1.66  Inference rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Ref     : 1
% 4.01/1.66  #Sup     : 146
% 4.01/1.66  #Fact    : 0
% 4.01/1.66  #Define  : 0
% 4.01/1.66  #Split   : 9
% 4.01/1.66  #Chain   : 0
% 4.01/1.66  #Close   : 0
% 4.01/1.66  
% 4.01/1.66  Ordering : KBO
% 4.01/1.66  
% 4.01/1.66  Simplification rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Subsume      : 10
% 4.01/1.66  #Demod        : 219
% 4.01/1.66  #Tautology    : 48
% 4.01/1.66  #SimpNegUnit  : 58
% 4.01/1.66  #BackRed      : 9
% 4.01/1.66  
% 4.01/1.66  #Partial instantiations: 0
% 4.01/1.66  #Strategies tried      : 1
% 4.01/1.66  
% 4.01/1.66  Timing (in seconds)
% 4.01/1.66  ----------------------
% 4.01/1.66  Preprocessing        : 0.42
% 4.01/1.66  Parsing              : 0.20
% 4.01/1.66  CNF conversion       : 0.06
% 4.01/1.66  Main loop            : 0.45
% 4.01/1.66  Inferencing          : 0.16
% 4.01/1.66  Reduction            : 0.14
% 4.01/1.66  Demodulation         : 0.10
% 4.01/1.66  BG Simplification    : 0.03
% 4.01/1.66  Subsumption          : 0.09
% 4.01/1.66  Abstraction          : 0.03
% 4.01/1.66  MUC search           : 0.00
% 4.01/1.66  Cooper               : 0.00
% 4.01/1.66  Total                : 0.92
% 4.01/1.66  Index Insertion      : 0.00
% 4.01/1.66  Index Deletion       : 0.00
% 4.01/1.66  Index Matching       : 0.00
% 4.01/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
