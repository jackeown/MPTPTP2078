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
% DateTime   : Thu Dec  3 10:18:09 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :  115 (1050 expanded)
%              Number of leaves         :   39 ( 382 expanded)
%              Depth                    :   24
%              Number of atoms          :  218 (3639 expanded)
%              Number of equality atoms :   37 ( 734 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_218,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_232,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_218])).

tff(c_52,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_233,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_52])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_105])).

tff(c_120,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_176,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_190,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_2439,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_xboole_0 = B_247
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2462,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2439])).

tff(c_2470,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_190,c_2462])).

tff(c_2471,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2470])).

tff(c_2501,plain,(
    ! [C_251,B_252] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_251),B_252,C_251),k1_relat_1(C_251))
      | v1_funct_2(C_251,k1_relat_1(C_251),B_252)
      | ~ v1_funct_1(C_251)
      | ~ v1_relat_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2513,plain,(
    ! [B_252] :
      ( r2_hidden('#skF_2'('#skF_4',B_252,'#skF_6'),k1_relat_1('#skF_6'))
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_252)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_2501])).

tff(c_2536,plain,(
    ! [B_253] :
      ( r2_hidden('#skF_2'('#skF_4',B_253,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60,c_2471,c_2471,c_2513])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2547,plain,(
    ! [B_253] :
      ( m1_subset_1('#skF_2'('#skF_4',B_253,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_253) ) ),
    inference(resolution,[status(thm)],[c_2536,c_8])).

tff(c_2811,plain,(
    ! [A_280,B_281,C_282,D_283] :
      ( k3_funct_2(A_280,B_281,C_282,D_283) = k1_funct_1(C_282,D_283)
      | ~ m1_subset_1(D_283,A_280)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_2(C_282,A_280,B_281)
      | ~ v1_funct_1(C_282)
      | v1_xboole_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2819,plain,(
    ! [B_281,C_282,B_253] :
      ( k3_funct_2('#skF_4',B_281,C_282,'#skF_2'('#skF_4',B_253,'#skF_6')) = k1_funct_1(C_282,'#skF_2'('#skF_4',B_253,'#skF_6'))
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_281)))
      | ~ v1_funct_2(C_282,'#skF_4',B_281)
      | ~ v1_funct_1(C_282)
      | v1_xboole_0('#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_253) ) ),
    inference(resolution,[status(thm)],[c_2547,c_2811])).

tff(c_2877,plain,(
    ! [B_287,C_288,B_289] :
      ( k3_funct_2('#skF_4',B_287,C_288,'#skF_2'('#skF_4',B_289,'#skF_6')) = k1_funct_1(C_288,'#skF_2'('#skF_4',B_289,'#skF_6'))
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_287)))
      | ~ v1_funct_2(C_288,'#skF_4',B_287)
      | ~ v1_funct_1(C_288)
      | v1_funct_2('#skF_6','#skF_4',B_289) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2819])).

tff(c_2893,plain,(
    ! [B_289] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_289,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_289,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_funct_2('#skF_6','#skF_4',B_289) ) ),
    inference(resolution,[status(thm)],[c_56,c_2877])).

tff(c_3625,plain,(
    ! [B_346] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_346,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_346,'#skF_6'))
      | v1_funct_2('#skF_6','#skF_4',B_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2893])).

tff(c_54,plain,(
    ! [E_48] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_48),'#skF_3')
      | ~ m1_subset_1(E_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3671,plain,(
    ! [B_353] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_353,'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_353,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3625,c_54])).

tff(c_2559,plain,(
    ! [C_256,B_257] :
      ( ~ r2_hidden(k1_funct_1(C_256,'#skF_2'(k1_relat_1(C_256),B_257,C_256)),B_257)
      | v1_funct_2(C_256,k1_relat_1(C_256),B_257)
      | ~ v1_funct_1(C_256)
      | ~ v1_relat_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2562,plain,(
    ! [B_257] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_257,'#skF_6')),B_257)
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_257)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_2559])).

tff(c_2564,plain,(
    ! [B_257] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_257,'#skF_6')),B_257)
      | v1_funct_2('#skF_6','#skF_4',B_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60,c_2471,c_2562])).

tff(c_3690,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3671,c_2564])).

tff(c_3694,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3690])).

tff(c_2658,plain,(
    ! [C_264,B_265] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_264),B_265,C_264),k1_relat_1(C_264))
      | m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_264),B_265)))
      | ~ v1_funct_1(C_264)
      | ~ v1_relat_1(C_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2670,plain,(
    ! [B_265] :
      ( r2_hidden('#skF_2'('#skF_4',B_265,'#skF_6'),k1_relat_1('#skF_6'))
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_265)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_2658])).

tff(c_2683,plain,(
    ! [B_266] :
      ( r2_hidden('#skF_2'('#skF_4',B_266,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_266))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60,c_2471,c_2471,c_2670])).

tff(c_24,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3007,plain,(
    ! [B_299] :
      ( k2_relset_1('#skF_4',B_299,'#skF_6') = k2_relat_1('#skF_6')
      | r2_hidden('#skF_2'('#skF_4',B_299,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2683,c_24])).

tff(c_3018,plain,(
    ! [B_299] :
      ( m1_subset_1('#skF_2'('#skF_4',B_299,'#skF_6'),'#skF_4')
      | k2_relset_1('#skF_4',B_299,'#skF_6') = k2_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3007,c_8])).

tff(c_3708,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3018,c_3694])).

tff(c_2678,plain,(
    ! [B_265] :
      ( r2_hidden('#skF_2'('#skF_4',B_265,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_265))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60,c_2471,c_2471,c_2670])).

tff(c_261,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1(k2_relset_1(A_93,B_94,C_95),k1_zfmisc_1(B_94))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2852,plain,(
    ! [A_284,B_285,C_286] :
      ( r1_tarski(k2_relset_1(A_284,B_285,C_286),B_285)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(resolution,[status(thm)],[c_261,c_10])).

tff(c_2974,plain,(
    ! [B_298] :
      ( r1_tarski(k2_relset_1('#skF_4',B_298,'#skF_6'),B_298)
      | r2_hidden('#skF_2'('#skF_4',B_298,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2678,c_2852])).

tff(c_3005,plain,(
    ! [B_298] :
      ( m1_subset_1('#skF_2'('#skF_4',B_298,'#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4',B_298,'#skF_6'),B_298) ) ),
    inference(resolution,[status(thm)],[c_2974,c_8])).

tff(c_3718,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3708,c_3005])).

tff(c_3732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_3694,c_3718])).

tff(c_3734,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3690])).

tff(c_38,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k3_funct_2(A_29,B_30,C_31,D_32) = k1_funct_1(C_31,D_32)
      | ~ m1_subset_1(D_32,A_29)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3747,plain,(
    ! [B_30,C_31] :
      ( k3_funct_2('#skF_4',B_30,C_31,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_31,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_30)))
      | ~ v1_funct_2(C_31,'#skF_4',B_30)
      | ~ v1_funct_1(C_31)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3734,c_38])).

tff(c_3814,plain,(
    ! [B_357,C_358] :
      ( k3_funct_2('#skF_4',B_357,C_358,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_358,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_357)))
      | ~ v1_funct_2(C_358,'#skF_4',B_357)
      | ~ v1_funct_1(C_358) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3747])).

tff(c_3839,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_3814])).

tff(c_3852,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3839])).

tff(c_3865,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3852,c_54])).

tff(c_3878,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_3865])).

tff(c_2743,plain,(
    ! [C_272,B_273] :
      ( ~ r2_hidden(k1_funct_1(C_272,'#skF_2'(k1_relat_1(C_272),B_273,C_272)),B_273)
      | m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_272),B_273)))
      | ~ v1_funct_1(C_272)
      | ~ v1_relat_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2746,plain,(
    ! [B_273] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_273,'#skF_6')),B_273)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_273)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_2743])).

tff(c_2748,plain,(
    ! [B_273] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_273,'#skF_6')),B_273)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_273))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60,c_2471,c_2746])).

tff(c_3902,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_3878,c_2748])).

tff(c_3982,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3902,c_24])).

tff(c_285,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(k2_relset_1(A_93,B_94,C_95),B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(resolution,[status(thm)],[c_261,c_10])).

tff(c_3975,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_3','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3902,c_285])).

tff(c_4030,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3982,c_3975])).

tff(c_4032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_4030])).

tff(c_4033,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2470])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(B_57,A_58)
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [A_60] :
      ( ~ r1_tarski(A_60,'#skF_1'(A_60))
      | v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_4050,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4033,c_89])).

tff(c_4054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.12  
% 5.84/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.13  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.84/2.13  
% 5.84/2.13  %Foreground sorts:
% 5.84/2.13  
% 5.84/2.13  
% 5.84/2.13  %Background operators:
% 5.84/2.13  
% 5.84/2.13  
% 5.84/2.13  %Foreground operators:
% 5.84/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.84/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.84/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.84/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.84/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.84/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.84/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.84/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.84/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.84/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.84/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.84/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.84/2.13  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.84/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.84/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.13  
% 6.09/2.14  tff(f_137, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 6.09/2.14  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.09/2.14  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.09/2.14  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.09/2.14  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.09/2.15  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.09/2.15  tff(f_115, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 6.09/2.15  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.09/2.15  tff(f_98, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 6.09/2.15  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.09/2.15  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.09/2.15  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.09/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.09/2.15  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.09/2.15  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_218, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.09/2.15  tff(c_232, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_218])).
% 6.09/2.15  tff(c_52, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_233, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_52])).
% 6.09/2.15  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.09/2.15  tff(c_105, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.09/2.15  tff(c_115, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_105])).
% 6.09/2.15  tff(c_120, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 6.09/2.15  tff(c_176, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.09/2.15  tff(c_190, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_176])).
% 6.09/2.15  tff(c_2439, plain, (![B_247, A_248, C_249]: (k1_xboole_0=B_247 | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.09/2.15  tff(c_2462, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_2439])).
% 6.09/2.15  tff(c_2470, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_190, c_2462])).
% 6.09/2.15  tff(c_2471, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2470])).
% 6.09/2.15  tff(c_2501, plain, (![C_251, B_252]: (r2_hidden('#skF_2'(k1_relat_1(C_251), B_252, C_251), k1_relat_1(C_251)) | v1_funct_2(C_251, k1_relat_1(C_251), B_252) | ~v1_funct_1(C_251) | ~v1_relat_1(C_251))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.09/2.15  tff(c_2513, plain, (![B_252]: (r2_hidden('#skF_2'('#skF_4', B_252, '#skF_6'), k1_relat_1('#skF_6')) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_252) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2471, c_2501])).
% 6.09/2.15  tff(c_2536, plain, (![B_253]: (r2_hidden('#skF_2'('#skF_4', B_253, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_253))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60, c_2471, c_2471, c_2513])).
% 6.09/2.15  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.09/2.15  tff(c_2547, plain, (![B_253]: (m1_subset_1('#skF_2'('#skF_4', B_253, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_253))), inference(resolution, [status(thm)], [c_2536, c_8])).
% 6.09/2.15  tff(c_2811, plain, (![A_280, B_281, C_282, D_283]: (k3_funct_2(A_280, B_281, C_282, D_283)=k1_funct_1(C_282, D_283) | ~m1_subset_1(D_283, A_280) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_funct_2(C_282, A_280, B_281) | ~v1_funct_1(C_282) | v1_xboole_0(A_280))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.09/2.15  tff(c_2819, plain, (![B_281, C_282, B_253]: (k3_funct_2('#skF_4', B_281, C_282, '#skF_2'('#skF_4', B_253, '#skF_6'))=k1_funct_1(C_282, '#skF_2'('#skF_4', B_253, '#skF_6')) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_281))) | ~v1_funct_2(C_282, '#skF_4', B_281) | ~v1_funct_1(C_282) | v1_xboole_0('#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_253))), inference(resolution, [status(thm)], [c_2547, c_2811])).
% 6.09/2.15  tff(c_2877, plain, (![B_287, C_288, B_289]: (k3_funct_2('#skF_4', B_287, C_288, '#skF_2'('#skF_4', B_289, '#skF_6'))=k1_funct_1(C_288, '#skF_2'('#skF_4', B_289, '#skF_6')) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_287))) | ~v1_funct_2(C_288, '#skF_4', B_287) | ~v1_funct_1(C_288) | v1_funct_2('#skF_6', '#skF_4', B_289))), inference(negUnitSimplification, [status(thm)], [c_64, c_2819])).
% 6.09/2.15  tff(c_2893, plain, (![B_289]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_289, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_289, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_funct_2('#skF_6', '#skF_4', B_289))), inference(resolution, [status(thm)], [c_56, c_2877])).
% 6.09/2.15  tff(c_3625, plain, (![B_346]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_346, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_346, '#skF_6')) | v1_funct_2('#skF_6', '#skF_4', B_346))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2893])).
% 6.09/2.15  tff(c_54, plain, (![E_48]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_48), '#skF_3') | ~m1_subset_1(E_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.09/2.15  tff(c_3671, plain, (![B_353]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_353, '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', B_353, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_353))), inference(superposition, [status(thm), theory('equality')], [c_3625, c_54])).
% 6.09/2.15  tff(c_2559, plain, (![C_256, B_257]: (~r2_hidden(k1_funct_1(C_256, '#skF_2'(k1_relat_1(C_256), B_257, C_256)), B_257) | v1_funct_2(C_256, k1_relat_1(C_256), B_257) | ~v1_funct_1(C_256) | ~v1_relat_1(C_256))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.09/2.15  tff(c_2562, plain, (![B_257]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_257, '#skF_6')), B_257) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_257) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2471, c_2559])).
% 6.09/2.15  tff(c_2564, plain, (![B_257]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_257, '#skF_6')), B_257) | v1_funct_2('#skF_6', '#skF_4', B_257))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60, c_2471, c_2562])).
% 6.09/2.15  tff(c_3690, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3671, c_2564])).
% 6.09/2.15  tff(c_3694, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3690])).
% 6.09/2.15  tff(c_2658, plain, (![C_264, B_265]: (r2_hidden('#skF_2'(k1_relat_1(C_264), B_265, C_264), k1_relat_1(C_264)) | m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_264), B_265))) | ~v1_funct_1(C_264) | ~v1_relat_1(C_264))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.09/2.15  tff(c_2670, plain, (![B_265]: (r2_hidden('#skF_2'('#skF_4', B_265, '#skF_6'), k1_relat_1('#skF_6')) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_265))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2471, c_2658])).
% 6.09/2.15  tff(c_2683, plain, (![B_266]: (r2_hidden('#skF_2'('#skF_4', B_266, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_266))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60, c_2471, c_2471, c_2670])).
% 6.09/2.15  tff(c_24, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.09/2.15  tff(c_3007, plain, (![B_299]: (k2_relset_1('#skF_4', B_299, '#skF_6')=k2_relat_1('#skF_6') | r2_hidden('#skF_2'('#skF_4', B_299, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_2683, c_24])).
% 6.09/2.15  tff(c_3018, plain, (![B_299]: (m1_subset_1('#skF_2'('#skF_4', B_299, '#skF_6'), '#skF_4') | k2_relset_1('#skF_4', B_299, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3007, c_8])).
% 6.09/2.15  tff(c_3708, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3018, c_3694])).
% 6.09/2.15  tff(c_2678, plain, (![B_265]: (r2_hidden('#skF_2'('#skF_4', B_265, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_265))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60, c_2471, c_2471, c_2670])).
% 6.09/2.15  tff(c_261, plain, (![A_93, B_94, C_95]: (m1_subset_1(k2_relset_1(A_93, B_94, C_95), k1_zfmisc_1(B_94)) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.09/2.15  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.09/2.15  tff(c_2852, plain, (![A_284, B_285, C_286]: (r1_tarski(k2_relset_1(A_284, B_285, C_286), B_285) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(resolution, [status(thm)], [c_261, c_10])).
% 6.09/2.15  tff(c_2974, plain, (![B_298]: (r1_tarski(k2_relset_1('#skF_4', B_298, '#skF_6'), B_298) | r2_hidden('#skF_2'('#skF_4', B_298, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_2678, c_2852])).
% 6.09/2.15  tff(c_3005, plain, (![B_298]: (m1_subset_1('#skF_2'('#skF_4', B_298, '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', B_298, '#skF_6'), B_298))), inference(resolution, [status(thm)], [c_2974, c_8])).
% 6.09/2.15  tff(c_3718, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3708, c_3005])).
% 6.09/2.15  tff(c_3732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_3694, c_3718])).
% 6.09/2.15  tff(c_3734, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_3690])).
% 6.09/2.15  tff(c_38, plain, (![A_29, B_30, C_31, D_32]: (k3_funct_2(A_29, B_30, C_31, D_32)=k1_funct_1(C_31, D_32) | ~m1_subset_1(D_32, A_29) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.09/2.15  tff(c_3747, plain, (![B_30, C_31]: (k3_funct_2('#skF_4', B_30, C_31, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_31, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_30))) | ~v1_funct_2(C_31, '#skF_4', B_30) | ~v1_funct_1(C_31) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_3734, c_38])).
% 6.09/2.15  tff(c_3814, plain, (![B_357, C_358]: (k3_funct_2('#skF_4', B_357, C_358, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_358, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_357))) | ~v1_funct_2(C_358, '#skF_4', B_357) | ~v1_funct_1(C_358))), inference(negUnitSimplification, [status(thm)], [c_64, c_3747])).
% 6.09/2.15  tff(c_3839, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_3814])).
% 6.09/2.15  tff(c_3852, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3839])).
% 6.09/2.15  tff(c_3865, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3852, c_54])).
% 6.09/2.15  tff(c_3878, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_3865])).
% 6.09/2.15  tff(c_2743, plain, (![C_272, B_273]: (~r2_hidden(k1_funct_1(C_272, '#skF_2'(k1_relat_1(C_272), B_273, C_272)), B_273) | m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_272), B_273))) | ~v1_funct_1(C_272) | ~v1_relat_1(C_272))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.09/2.15  tff(c_2746, plain, (![B_273]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_273, '#skF_6')), B_273) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_273))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2471, c_2743])).
% 6.09/2.15  tff(c_2748, plain, (![B_273]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_273, '#skF_6')), B_273) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_273))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60, c_2471, c_2746])).
% 6.09/2.15  tff(c_3902, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_3878, c_2748])).
% 6.09/2.15  tff(c_3982, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3902, c_24])).
% 6.09/2.15  tff(c_285, plain, (![A_93, B_94, C_95]: (r1_tarski(k2_relset_1(A_93, B_94, C_95), B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(resolution, [status(thm)], [c_261, c_10])).
% 6.09/2.15  tff(c_3975, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_3', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_3902, c_285])).
% 6.09/2.15  tff(c_4030, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3982, c_3975])).
% 6.09/2.15  tff(c_4032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_4030])).
% 6.09/2.15  tff(c_4033, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2470])).
% 6.09/2.15  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.09/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.09/2.15  tff(c_78, plain, (![B_57, A_58]: (~r1_tarski(B_57, A_58) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.09/2.15  tff(c_84, plain, (![A_60]: (~r1_tarski(A_60, '#skF_1'(A_60)) | v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_4, c_78])).
% 6.09/2.15  tff(c_89, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_84])).
% 6.09/2.15  tff(c_4050, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4033, c_89])).
% 6.09/2.15  tff(c_4054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4050])).
% 6.09/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.15  
% 6.09/2.15  Inference rules
% 6.09/2.15  ----------------------
% 6.09/2.15  #Ref     : 0
% 6.09/2.15  #Sup     : 792
% 6.09/2.15  #Fact    : 0
% 6.09/2.15  #Define  : 0
% 6.09/2.15  #Split   : 19
% 6.09/2.15  #Chain   : 0
% 6.09/2.15  #Close   : 0
% 6.09/2.15  
% 6.09/2.15  Ordering : KBO
% 6.09/2.15  
% 6.09/2.15  Simplification rules
% 6.09/2.15  ----------------------
% 6.09/2.15  #Subsume      : 174
% 6.09/2.15  #Demod        : 663
% 6.09/2.15  #Tautology    : 185
% 6.09/2.15  #SimpNegUnit  : 70
% 6.09/2.15  #BackRed      : 83
% 6.09/2.15  
% 6.09/2.15  #Partial instantiations: 0
% 6.09/2.15  #Strategies tried      : 1
% 6.09/2.15  
% 6.09/2.15  Timing (in seconds)
% 6.09/2.15  ----------------------
% 6.09/2.15  Preprocessing        : 0.36
% 6.09/2.15  Parsing              : 0.19
% 6.09/2.15  CNF conversion       : 0.03
% 6.09/2.15  Main loop            : 1.02
% 6.09/2.15  Inferencing          : 0.35
% 6.09/2.15  Reduction            : 0.34
% 6.09/2.15  Demodulation         : 0.23
% 6.09/2.15  BG Simplification    : 0.05
% 6.09/2.15  Subsumption          : 0.17
% 6.09/2.15  Abstraction          : 0.06
% 6.09/2.15  MUC search           : 0.00
% 6.09/2.15  Cooper               : 0.00
% 6.09/2.15  Total                : 1.41
% 6.09/2.15  Index Insertion      : 0.00
% 6.09/2.15  Index Deletion       : 0.00
% 6.09/2.15  Index Matching       : 0.00
% 6.09/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
