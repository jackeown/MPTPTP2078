%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:37 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  208 (1427 expanded)
%              Number of leaves         :   26 ( 531 expanded)
%              Depth                    :   14
%              Number of atoms          :  718 (8586 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_filter_1 > k1_domain_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_domain_1,type,(
    k1_domain_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_binop_1,type,(
    r3_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r1_binop_1,type,(
    r1_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_filter_1,type,(
    k6_filter_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_binop_1,type,(
    r2_binop_1: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( m1_subset_1(D,B)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,k2_zfmisc_1(A,A),A)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                           => ( ( r3_binop_1(A,C,E)
                                & r3_binop_1(B,D,F) )
                            <=> r3_binop_1(k2_zfmisc_1(A,B),k1_domain_1(A,B,C,D),k6_filter_1(A,B,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_filter_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r3_binop_1(A,B,C)
          <=> ( r1_binop_1(A,B,C)
              & r2_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(D)
        & v1_funct_2(D,k2_zfmisc_1(B,B),B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
     => ( v1_funct_1(k6_filter_1(A,B,C,D))
        & v1_funct_2(k6_filter_1(A,B,C,D),k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B))
        & m1_subset_1(k6_filter_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_filter_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => m1_subset_1(k1_domain_1(A,B,C,D),k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_domain_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m1_subset_1(D,B)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(A,A),A)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r1_binop_1(A,C,E)
                              & r1_binop_1(B,D,F) )
                          <=> r1_binop_1(k2_zfmisc_1(A,B),k1_domain_1(A,B,C,D),k6_filter_1(A,B,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_filter_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m1_subset_1(D,B)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(A,A),A)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r2_binop_1(A,C,E)
                              & r2_binop_1(B,D,F) )
                          <=> r2_binop_1(k2_zfmisc_1(A,B),k1_domain_1(A,B,C,D),k6_filter_1(A,B,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_filter_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_30,plain,(
    v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_475,plain,(
    ! [A_320,B_321,C_322] :
      ( r3_binop_1(A_320,B_321,C_322)
      | ~ r2_binop_1(A_320,B_321,C_322)
      | ~ r1_binop_1(A_320,B_321,C_322)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_320,A_320),A_320)))
      | ~ v1_funct_2(C_322,k2_zfmisc_1(A_320,A_320),A_320)
      | ~ v1_funct_1(C_322)
      | ~ m1_subset_1(B_321,A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_477,plain,(
    ! [B_321] :
      ( r3_binop_1('#skF_2',B_321,'#skF_6')
      | ~ r2_binop_1('#skF_2',B_321,'#skF_6')
      | ~ r1_binop_1('#skF_2',B_321,'#skF_6')
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(B_321,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_475])).

tff(c_497,plain,(
    ! [B_327] :
      ( r3_binop_1('#skF_2',B_327,'#skF_6')
      | ~ r2_binop_1('#skF_2',B_327,'#skF_6')
      | ~ r1_binop_1('#skF_2',B_327,'#skF_6')
      | ~ m1_subset_1(B_327,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_477])).

tff(c_73,plain,(
    ! [A_206,B_207,C_208] :
      ( r3_binop_1(A_206,B_207,C_208)
      | ~ r2_binop_1(A_206,B_207,C_208)
      | ~ r1_binop_1(A_206,B_207,C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_206,A_206),A_206)))
      | ~ v1_funct_2(C_208,k2_zfmisc_1(A_206,A_206),A_206)
      | ~ v1_funct_1(C_208)
      | ~ m1_subset_1(B_207,A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [B_207] :
      ( r3_binop_1('#skF_1',B_207,'#skF_5')
      | ~ r2_binop_1('#skF_1',B_207,'#skF_5')
      | ~ r1_binop_1('#skF_1',B_207,'#skF_5')
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(B_207,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_95,plain,(
    ! [B_210] :
      ( r3_binop_1('#skF_1',B_210,'#skF_5')
      | ~ r2_binop_1('#skF_1',B_210,'#skF_5')
      | ~ r1_binop_1('#skF_1',B_210,'#skF_5')
      | ~ m1_subset_1(B_210,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_77])).

tff(c_56,plain,
    ( r3_binop_1('#skF_2','#skF_4','#skF_6')
    | r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_59,plain,(
    r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( ~ r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ r3_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_63,plain,
    ( ~ r3_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48])).

tff(c_64,plain,(
    ~ r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_102,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_64])).

tff(c_111,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ r1_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_112,plain,(
    ~ r1_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k6_filter_1(A_9,B_10,C_11,D_12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1(A_9,B_10)),k2_zfmisc_1(A_9,B_10))))
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_10,B_10),B_10)))
      | ~ v1_funct_2(D_12,k2_zfmisc_1(B_10,B_10),B_10)
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_11,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( v1_funct_2(k6_filter_1(A_9,B_10,C_11,D_12),k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1(A_9,B_10)),k2_zfmisc_1(A_9,B_10))
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_10,B_10),B_10)))
      | ~ v1_funct_2(D_12,k2_zfmisc_1(B_10,B_10),B_10)
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_11,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k1_domain_1(A_1,B_2,C_3,D_4),k2_zfmisc_1(A_1,B_2))
      | ~ m1_subset_1(D_4,B_2)
      | ~ m1_subset_1(C_3,A_1)
      | v1_xboole_0(B_2)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( v1_funct_1(k6_filter_1(A_211,B_212,C_213,D_214))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_212,B_212),B_212)))
      | ~ v1_funct_2(D_214,k2_zfmisc_1(B_212,B_212),B_212)
      | ~ v1_funct_1(D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_211,A_211),A_211)))
      | ~ v1_funct_2(C_213,k2_zfmisc_1(A_211,A_211),A_211)
      | ~ v1_funct_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,(
    ! [A_211,C_213] :
      ( v1_funct_1(k6_filter_1(A_211,'#skF_2',C_213,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_211,A_211),A_211)))
      | ~ v1_funct_2(C_213,k2_zfmisc_1(A_211,A_211),A_211)
      | ~ v1_funct_1(C_213) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_124,plain,(
    ! [A_215,C_216] :
      ( v1_funct_1(k6_filter_1(A_215,'#skF_2',C_216,'#skF_6'))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_215,A_215),A_215)))
      | ~ v1_funct_2(C_216,k2_zfmisc_1(A_215,A_215),A_215)
      | ~ v1_funct_1(C_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_115])).

tff(c_130,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_136,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_130])).

tff(c_65,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_binop_1(A_200,B_201,C_202)
      | ~ r3_binop_1(A_200,B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_200,A_200),A_200)))
      | ~ v1_funct_2(C_202,k2_zfmisc_1(A_200,A_200),A_200)
      | ~ v1_funct_1(C_202)
      | ~ m1_subset_1(B_201,A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_65])).

tff(c_171,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_68])).

tff(c_172,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_175,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_172])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_175])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_178])).

tff(c_182,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_69,plain,(
    ! [A_203,B_204,C_205] :
      ( r2_binop_1(A_203,B_204,C_205)
      | ~ r3_binop_1(A_203,B_204,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_203,A_203),A_203)))
      | ~ v1_funct_2(C_205,k2_zfmisc_1(A_203,A_203),A_203)
      | ~ v1_funct_1(C_205)
      | ~ m1_subset_1(B_204,A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_69])).

tff(c_184,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_136,c_72])).

tff(c_185,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_188])).

tff(c_193,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_195,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_198,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_198])).

tff(c_204,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_194,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_181,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_317,plain,(
    r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_194,c_181])).

tff(c_20,plain,(
    ! [F_75,E_73,A_13,C_61,B_45,D_69] :
      ( r1_binop_1(A_13,C_61,E_73)
      | ~ r1_binop_1(k2_zfmisc_1(A_13,B_45),k1_domain_1(A_13,B_45,C_61,D_69),k6_filter_1(A_13,B_45,E_73,F_75))
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45,B_45),B_45)))
      | ~ v1_funct_2(F_75,k2_zfmisc_1(B_45,B_45),B_45)
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(E_73,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(E_73)
      | ~ m1_subset_1(D_69,B_45)
      | ~ m1_subset_1(C_61,A_13)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_323,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_317,c_20])).

tff(c_330,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_5')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_323])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_112,c_330])).

tff(c_333,plain,(
    ~ r2_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_335,plain,(
    ! [A_274,B_275,C_276,D_277] :
      ( v1_funct_1(k6_filter_1(A_274,B_275,C_276,D_277))
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_275,B_275),B_275)))
      | ~ v1_funct_2(D_277,k2_zfmisc_1(B_275,B_275),B_275)
      | ~ v1_funct_1(D_277)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_274,A_274),A_274)))
      | ~ v1_funct_2(C_276,k2_zfmisc_1(A_274,A_274),A_274)
      | ~ v1_funct_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_337,plain,(
    ! [A_274,C_276] :
      ( v1_funct_1(k6_filter_1(A_274,'#skF_2',C_276,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_274,A_274),A_274)))
      | ~ v1_funct_2(C_276,k2_zfmisc_1(A_274,A_274),A_274)
      | ~ v1_funct_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_28,c_335])).

tff(c_346,plain,(
    ! [A_278,C_279] :
      ( v1_funct_1(k6_filter_1(A_278,'#skF_2',C_279,'#skF_6'))
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_278,A_278),A_278)))
      | ~ v1_funct_2(C_279,k2_zfmisc_1(A_278,A_278),A_278)
      | ~ v1_funct_1(C_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_337])).

tff(c_352,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_346])).

tff(c_358,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_352])).

tff(c_393,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_68])).

tff(c_394,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_397,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_394])).

tff(c_400,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_397])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_400])).

tff(c_404,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_406,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_358,c_72])).

tff(c_407,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_410,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_407])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_410])).

tff(c_415,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_417,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_420,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_417])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_420])).

tff(c_425,plain,(
    r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_26,plain,(
    ! [A_76,F_138,B_108,D_132,E_136,C_124] :
      ( r2_binop_1(A_76,C_124,E_136)
      | ~ r2_binop_1(k2_zfmisc_1(A_76,B_108),k1_domain_1(A_76,B_108,C_124,D_132),k6_filter_1(A_76,B_108,E_136,F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108,B_108),B_108)))
      | ~ v1_funct_2(F_138,k2_zfmisc_1(B_108,B_108),B_108)
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76,A_76),A_76)))
      | ~ v1_funct_2(E_136,k2_zfmisc_1(A_76,A_76),A_76)
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(D_132,B_108)
      | ~ m1_subset_1(C_124,A_76)
      | v1_xboole_0(B_108)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_432,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_425,c_26])).

tff(c_439,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_5')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_432])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_333,c_439])).

tff(c_442,plain,(
    ~ r3_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_504,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_497,c_442])).

tff(c_513,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r1_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_504])).

tff(c_514,plain,(
    ~ r1_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_486,plain,(
    ! [A_323,B_324,C_325,D_326] :
      ( v1_funct_1(k6_filter_1(A_323,B_324,C_325,D_326))
      | ~ m1_subset_1(D_326,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_324,B_324),B_324)))
      | ~ v1_funct_2(D_326,k2_zfmisc_1(B_324,B_324),B_324)
      | ~ v1_funct_1(D_326)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_323,A_323),A_323)))
      | ~ v1_funct_2(C_325,k2_zfmisc_1(A_323,A_323),A_323)
      | ~ v1_funct_1(C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_488,plain,(
    ! [A_323,C_325] :
      ( v1_funct_1(k6_filter_1(A_323,'#skF_2',C_325,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_323,A_323),A_323)))
      | ~ v1_funct_2(C_325,k2_zfmisc_1(A_323,A_323),A_323)
      | ~ v1_funct_1(C_325) ) ),
    inference(resolution,[status(thm)],[c_28,c_486])).

tff(c_539,plain,(
    ! [A_331,C_332] :
      ( v1_funct_1(k6_filter_1(A_331,'#skF_2',C_332,'#skF_6'))
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_331,A_331),A_331)))
      | ~ v1_funct_2(C_332,k2_zfmisc_1(A_331,A_331),A_331)
      | ~ v1_funct_1(C_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_488])).

tff(c_545,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_539])).

tff(c_551,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_545])).

tff(c_444,plain,(
    ! [A_314,B_315,C_316] :
      ( r2_binop_1(A_314,B_315,C_316)
      | ~ r3_binop_1(A_314,B_315,C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_314,A_314),A_314)))
      | ~ v1_funct_2(C_316,k2_zfmisc_1(A_314,A_314),A_314)
      | ~ v1_funct_1(C_316)
      | ~ m1_subset_1(B_315,A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_452,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_444])).

tff(c_453,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_456,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_453])).

tff(c_459,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_456])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_459])).

tff(c_462,plain,
    ( ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_569,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_462])).

tff(c_570,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_585,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_570])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_585])).

tff(c_591,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_493,plain,(
    ! [A_323,C_325] :
      ( v1_funct_1(k6_filter_1(A_323,'#skF_2',C_325,'#skF_6'))
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_323,A_323),A_323)))
      | ~ v1_funct_2(C_325,k2_zfmisc_1(A_323,A_323),A_323)
      | ~ v1_funct_1(C_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_488])).

tff(c_594,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_2',k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),'#skF_6'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_591,c_493])).

tff(c_604,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_2',k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),'#skF_6'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_594])).

tff(c_614,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_604])).

tff(c_618,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_614])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_618])).

tff(c_624,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_604])).

tff(c_463,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_464,plain,(
    ! [A_317,B_318,C_319] :
      ( r1_binop_1(A_317,B_318,C_319)
      | ~ r3_binop_1(A_317,B_318,C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_317,A_317),A_317)))
      | ~ v1_funct_2(C_319,k2_zfmisc_1(A_317,A_317),A_317)
      | ~ v1_funct_1(C_319)
      | ~ m1_subset_1(B_318,A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_468,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_464])).

tff(c_474,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_468])).

tff(c_626,plain,(
    r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_624,c_591,c_474])).

tff(c_883,plain,(
    ! [C_396,B_399,F_397,E_400,D_401,A_398] :
      ( r1_binop_1(B_399,D_401,F_397)
      | ~ r1_binop_1(k2_zfmisc_1(A_398,B_399),k1_domain_1(A_398,B_399,C_396,D_401),k6_filter_1(A_398,B_399,E_400,F_397))
      | ~ m1_subset_1(F_397,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_399,B_399),B_399)))
      | ~ v1_funct_2(F_397,k2_zfmisc_1(B_399,B_399),B_399)
      | ~ v1_funct_1(F_397)
      | ~ m1_subset_1(E_400,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_398,A_398),A_398)))
      | ~ v1_funct_2(E_400,k2_zfmisc_1(A_398,A_398),A_398)
      | ~ v1_funct_1(E_400)
      | ~ m1_subset_1(D_401,B_399)
      | ~ m1_subset_1(C_396,A_398)
      | v1_xboole_0(B_399)
      | v1_xboole_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_886,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_626,c_883])).

tff(c_889,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_6')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_886])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_514,c_889])).

tff(c_892,plain,(
    ~ r2_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_905,plain,(
    ! [A_403,C_404] :
      ( v1_funct_1(k6_filter_1(A_403,'#skF_2',C_404,'#skF_6'))
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_403,A_403),A_403)))
      | ~ v1_funct_2(C_404,k2_zfmisc_1(A_403,A_403),A_403)
      | ~ v1_funct_1(C_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_488])).

tff(c_911,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_905])).

tff(c_917,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_911])).

tff(c_948,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_474])).

tff(c_949,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_952,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_949])).

tff(c_956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_952])).

tff(c_958,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_960,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_462])).

tff(c_961,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_964,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_961])).

tff(c_968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_964])).

tff(c_969,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_1018,plain,(
    r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_969])).

tff(c_1055,plain,(
    ! [D_439,A_440,C_441,B_437,F_436,E_438] :
      ( r2_binop_1(B_437,D_439,F_436)
      | ~ r2_binop_1(k2_zfmisc_1(A_440,B_437),k1_domain_1(A_440,B_437,C_441,D_439),k6_filter_1(A_440,B_437,E_438,F_436))
      | ~ m1_subset_1(F_436,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_437,B_437),B_437)))
      | ~ v1_funct_2(F_436,k2_zfmisc_1(B_437,B_437),B_437)
      | ~ v1_funct_1(F_436)
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_440,A_440),A_440)))
      | ~ v1_funct_2(E_438,k2_zfmisc_1(A_440,A_440),A_440)
      | ~ v1_funct_1(E_438)
      | ~ m1_subset_1(D_439,B_437)
      | ~ m1_subset_1(C_441,A_440)
      | v1_xboole_0(B_437)
      | v1_xboole_0(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1058,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1018,c_1055])).

tff(c_1061,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_6')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_1058])).

tff(c_1063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_892,c_1061])).

tff(c_1065,plain,(
    ~ r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( r3_binop_1('#skF_1','#skF_3','#skF_5')
    | r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1066,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_58])).

tff(c_1081,plain,(
    ! [A_449,B_450,C_451] :
      ( r1_binop_1(A_449,B_450,C_451)
      | ~ r3_binop_1(A_449,B_450,C_451)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_449,A_449),A_449)))
      | ~ v1_funct_2(C_451,k2_zfmisc_1(A_449,A_449),A_449)
      | ~ v1_funct_1(C_451)
      | ~ m1_subset_1(B_450,A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1083,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1066,c_1081])).

tff(c_1088,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_34,c_1083])).

tff(c_1064,plain,(
    r3_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1085,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1064,c_1081])).

tff(c_1091,plain,(
    r1_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_30,c_28,c_1085])).

tff(c_16,plain,(
    ! [F_75,E_73,A_13,C_61,B_45,D_69] :
      ( r1_binop_1(k2_zfmisc_1(A_13,B_45),k1_domain_1(A_13,B_45,C_61,D_69),k6_filter_1(A_13,B_45,E_73,F_75))
      | ~ r1_binop_1(B_45,D_69,F_75)
      | ~ r1_binop_1(A_13,C_61,E_73)
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45,B_45),B_45)))
      | ~ v1_funct_2(F_75,k2_zfmisc_1(B_45,B_45),B_45)
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(E_73,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(E_73)
      | ~ m1_subset_1(D_69,B_45)
      | ~ m1_subset_1(C_61,A_13)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1070,plain,(
    ! [A_446,B_447,C_448] :
      ( r2_binop_1(A_446,B_447,C_448)
      | ~ r3_binop_1(A_446,B_447,C_448)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_446,A_446),A_446)))
      | ~ v1_funct_2(C_448,k2_zfmisc_1(A_446,A_446),A_446)
      | ~ v1_funct_1(C_448)
      | ~ m1_subset_1(B_447,A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1072,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1066,c_1070])).

tff(c_1077,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_34,c_1072])).

tff(c_1074,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1064,c_1070])).

tff(c_1080,plain,(
    r2_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_30,c_28,c_1074])).

tff(c_22,plain,(
    ! [A_76,F_138,B_108,D_132,E_136,C_124] :
      ( r2_binop_1(k2_zfmisc_1(A_76,B_108),k1_domain_1(A_76,B_108,C_124,D_132),k6_filter_1(A_76,B_108,E_136,F_138))
      | ~ r2_binop_1(B_108,D_132,F_138)
      | ~ r2_binop_1(A_76,C_124,E_136)
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108,B_108),B_108)))
      | ~ v1_funct_2(F_138,k2_zfmisc_1(B_108,B_108),B_108)
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76,A_76),A_76)))
      | ~ v1_funct_2(E_136,k2_zfmisc_1(A_76,A_76),A_76)
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(D_132,B_108)
      | ~ m1_subset_1(C_124,A_76)
      | v1_xboole_0(B_108)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1125,plain,(
    ! [A_457,B_458,C_459,D_460] :
      ( v1_funct_1(k6_filter_1(A_457,B_458,C_459,D_460))
      | ~ m1_subset_1(D_460,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_458,B_458),B_458)))
      | ~ v1_funct_2(D_460,k2_zfmisc_1(B_458,B_458),B_458)
      | ~ v1_funct_1(D_460)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_457,A_457),A_457)))
      | ~ v1_funct_2(C_459,k2_zfmisc_1(A_457,A_457),A_457)
      | ~ v1_funct_1(C_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1127,plain,(
    ! [A_457,C_459] :
      ( v1_funct_1(k6_filter_1(A_457,'#skF_2',C_459,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_457,A_457),A_457)))
      | ~ v1_funct_2(C_459,k2_zfmisc_1(A_457,A_457),A_457)
      | ~ v1_funct_1(C_459) ) ),
    inference(resolution,[status(thm)],[c_28,c_1125])).

tff(c_1136,plain,(
    ! [A_461,C_462] :
      ( v1_funct_1(k6_filter_1(A_461,'#skF_2',C_462,'#skF_6'))
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_461,A_461),A_461)))
      | ~ v1_funct_2(C_462,k2_zfmisc_1(A_461,A_461),A_461)
      | ~ v1_funct_1(C_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1127])).

tff(c_1142,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1136])).

tff(c_1148,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1142])).

tff(c_1163,plain,(
    ! [A_469,B_470,C_471,D_472] :
      ( m1_subset_1(k6_filter_1(A_469,B_470,C_471,D_472),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_469,B_470),k2_zfmisc_1(A_469,B_470)),k2_zfmisc_1(A_469,B_470))))
      | ~ m1_subset_1(D_472,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_470,B_470),B_470)))
      | ~ v1_funct_2(D_472,k2_zfmisc_1(B_470,B_470),B_470)
      | ~ v1_funct_1(D_472)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_469,A_469),A_469)))
      | ~ v1_funct_2(C_471,k2_zfmisc_1(A_469,A_469),A_469)
      | ~ v1_funct_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_5,B_6,C_8] :
      ( r3_binop_1(A_5,B_6,C_8)
      | ~ r2_binop_1(A_5,B_6,C_8)
      | ~ r1_binop_1(A_5,B_6,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5,A_5),A_5)))
      | ~ v1_funct_2(C_8,k2_zfmisc_1(A_5,A_5),A_5)
      | ~ v1_funct_1(C_8)
      | ~ m1_subset_1(B_6,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1338,plain,(
    ! [D_552,B_551,B_553,A_550,C_549] :
      ( r3_binop_1(k2_zfmisc_1(A_550,B_553),B_551,k6_filter_1(A_550,B_553,C_549,D_552))
      | ~ r2_binop_1(k2_zfmisc_1(A_550,B_553),B_551,k6_filter_1(A_550,B_553,C_549,D_552))
      | ~ r1_binop_1(k2_zfmisc_1(A_550,B_553),B_551,k6_filter_1(A_550,B_553,C_549,D_552))
      | ~ v1_funct_2(k6_filter_1(A_550,B_553,C_549,D_552),k2_zfmisc_1(k2_zfmisc_1(A_550,B_553),k2_zfmisc_1(A_550,B_553)),k2_zfmisc_1(A_550,B_553))
      | ~ v1_funct_1(k6_filter_1(A_550,B_553,C_549,D_552))
      | ~ m1_subset_1(B_551,k2_zfmisc_1(A_550,B_553))
      | ~ m1_subset_1(D_552,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_553,B_553),B_553)))
      | ~ v1_funct_2(D_552,k2_zfmisc_1(B_553,B_553),B_553)
      | ~ v1_funct_1(D_552)
      | ~ m1_subset_1(C_549,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_550,A_550),A_550)))
      | ~ v1_funct_2(C_549,k2_zfmisc_1(A_550,A_550),A_550)
      | ~ v1_funct_1(C_549) ) ),
    inference(resolution,[status(thm)],[c_1163,c_4])).

tff(c_1407,plain,(
    ! [B_568,C_565,A_567,B_564,D_566] :
      ( r3_binop_1(k2_zfmisc_1(A_567,B_564),B_568,k6_filter_1(A_567,B_564,C_565,D_566))
      | ~ r2_binop_1(k2_zfmisc_1(A_567,B_564),B_568,k6_filter_1(A_567,B_564,C_565,D_566))
      | ~ r1_binop_1(k2_zfmisc_1(A_567,B_564),B_568,k6_filter_1(A_567,B_564,C_565,D_566))
      | ~ v1_funct_1(k6_filter_1(A_567,B_564,C_565,D_566))
      | ~ m1_subset_1(B_568,k2_zfmisc_1(A_567,B_564))
      | ~ m1_subset_1(D_566,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_564,B_564),B_564)))
      | ~ v1_funct_2(D_566,k2_zfmisc_1(B_564,B_564),B_564)
      | ~ v1_funct_1(D_566)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_567,A_567),A_567)))
      | ~ v1_funct_2(C_565,k2_zfmisc_1(A_567,A_567),A_567)
      | ~ v1_funct_1(C_565) ) ),
    inference(resolution,[status(thm)],[c_12,c_1338])).

tff(c_1411,plain,(
    ! [A_567,B_568,C_565] :
      ( r3_binop_1(k2_zfmisc_1(A_567,'#skF_2'),B_568,k6_filter_1(A_567,'#skF_2',C_565,'#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1(A_567,'#skF_2'),B_568,k6_filter_1(A_567,'#skF_2',C_565,'#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1(A_567,'#skF_2'),B_568,k6_filter_1(A_567,'#skF_2',C_565,'#skF_6'))
      | ~ v1_funct_1(k6_filter_1(A_567,'#skF_2',C_565,'#skF_6'))
      | ~ m1_subset_1(B_568,k2_zfmisc_1(A_567,'#skF_2'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_565,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_567,A_567),A_567)))
      | ~ v1_funct_2(C_565,k2_zfmisc_1(A_567,A_567),A_567)
      | ~ v1_funct_1(C_565) ) ),
    inference(resolution,[status(thm)],[c_28,c_1407])).

tff(c_1474,plain,(
    ! [A_576,B_577,C_578] :
      ( r3_binop_1(k2_zfmisc_1(A_576,'#skF_2'),B_577,k6_filter_1(A_576,'#skF_2',C_578,'#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1(A_576,'#skF_2'),B_577,k6_filter_1(A_576,'#skF_2',C_578,'#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1(A_576,'#skF_2'),B_577,k6_filter_1(A_576,'#skF_2',C_578,'#skF_6'))
      | ~ v1_funct_1(k6_filter_1(A_576,'#skF_2',C_578,'#skF_6'))
      | ~ m1_subset_1(B_577,k2_zfmisc_1(A_576,'#skF_2'))
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_576,A_576),A_576)))
      | ~ v1_funct_2(C_578,k2_zfmisc_1(A_576,A_576),A_576)
      | ~ v1_funct_1(C_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1411])).

tff(c_1480,plain,(
    ! [B_577] :
      ( r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_577,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_577,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_577,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_577,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_1474])).

tff(c_1503,plain,(
    ! [B_588] :
      ( r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_588,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_588,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_588,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_588,k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1148,c_1480])).

tff(c_1517,plain,
    ( ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1503,c_1065])).

tff(c_1518,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1517])).

tff(c_1521,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1518])).

tff(c_1524,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1521])).

tff(c_1526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_1524])).

tff(c_1527,plain,
    ( ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_1529,plain,(
    ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1527])).

tff(c_1532,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1529])).

tff(c_1535,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_1077,c_1080,c_1532])).

tff(c_1537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_1535])).

tff(c_1538,plain,(
    ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1527])).

tff(c_1542,plain,
    ( ~ r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1538])).

tff(c_1545,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_1088,c_1091,c_1542])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_1545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.91  
% 5.06/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.91  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_filter_1 > k1_domain_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.06/1.91  
% 5.06/1.91  %Foreground sorts:
% 5.06/1.91  
% 5.06/1.91  
% 5.06/1.91  %Background operators:
% 5.06/1.91  
% 5.06/1.91  
% 5.06/1.91  %Foreground operators:
% 5.06/1.91  tff(k1_domain_1, type, k1_domain_1: ($i * $i * $i * $i) > $i).
% 5.06/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.91  tff('#skF_5', type, '#skF_5': $i).
% 5.06/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.06/1.91  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 5.06/1.91  tff('#skF_6', type, '#skF_6': $i).
% 5.06/1.91  tff('#skF_2', type, '#skF_2': $i).
% 5.06/1.91  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 5.06/1.91  tff('#skF_3', type, '#skF_3': $i).
% 5.06/1.91  tff('#skF_1', type, '#skF_1': $i).
% 5.06/1.91  tff(k6_filter_1, type, k6_filter_1: ($i * $i * $i * $i) > $i).
% 5.06/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.06/1.91  tff('#skF_4', type, '#skF_4': $i).
% 5.06/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.06/1.91  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 5.06/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/1.91  
% 5.06/1.95  tff(f_170, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, B) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, k2_zfmisc_1(A, A), A)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, k2_zfmisc_1(B, B), B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((r3_binop_1(A, C, E) & r3_binop_1(B, D, F)) <=> r3_binop_1(k2_zfmisc_1(A, B), k1_domain_1(A, B, C, D), k6_filter_1(A, B, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_filter_1)).
% 5.06/1.95  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_binop_1)).
% 5.06/1.95  tff(f_70, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) & v1_funct_1(D)) & v1_funct_2(D, k2_zfmisc_1(B, B), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((v1_funct_1(k6_filter_1(A, B, C, D)) & v1_funct_2(k6_filter_1(A, B, C, D), k2_zfmisc_1(k2_zfmisc_1(A, B), k2_zfmisc_1(A, B)), k2_zfmisc_1(A, B))) & m1_subset_1(k6_filter_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), k2_zfmisc_1(A, B)), k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_filter_1)).
% 5.06/1.95  tff(f_37, axiom, (![A, B, C, D]: ((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(C, A)) & m1_subset_1(D, B)) => m1_subset_1(k1_domain_1(A, B, C, D), k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_domain_1)).
% 5.06/1.95  tff(f_103, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, B) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, k2_zfmisc_1(A, A), A)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, k2_zfmisc_1(B, B), B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((r1_binop_1(A, C, E) & r1_binop_1(B, D, F)) <=> r1_binop_1(k2_zfmisc_1(A, B), k1_domain_1(A, B, C, D), k6_filter_1(A, B, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_filter_1)).
% 5.06/1.95  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, B) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, k2_zfmisc_1(A, A), A)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, k2_zfmisc_1(B, B), B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((r2_binop_1(A, C, E) & r2_binop_1(B, D, F)) <=> r2_binop_1(k2_zfmisc_1(A, B), k1_domain_1(A, B, C, D), k6_filter_1(A, B, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_filter_1)).
% 5.06/1.95  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_42, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_40, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_36, plain, (v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_32, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_30, plain, (v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_475, plain, (![A_320, B_321, C_322]: (r3_binop_1(A_320, B_321, C_322) | ~r2_binop_1(A_320, B_321, C_322) | ~r1_binop_1(A_320, B_321, C_322) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_320, A_320), A_320))) | ~v1_funct_2(C_322, k2_zfmisc_1(A_320, A_320), A_320) | ~v1_funct_1(C_322) | ~m1_subset_1(B_321, A_320))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_477, plain, (![B_321]: (r3_binop_1('#skF_2', B_321, '#skF_6') | ~r2_binop_1('#skF_2', B_321, '#skF_6') | ~r1_binop_1('#skF_2', B_321, '#skF_6') | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(B_321, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_475])).
% 5.06/1.95  tff(c_497, plain, (![B_327]: (r3_binop_1('#skF_2', B_327, '#skF_6') | ~r2_binop_1('#skF_2', B_327, '#skF_6') | ~r1_binop_1('#skF_2', B_327, '#skF_6') | ~m1_subset_1(B_327, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_477])).
% 5.06/1.95  tff(c_73, plain, (![A_206, B_207, C_208]: (r3_binop_1(A_206, B_207, C_208) | ~r2_binop_1(A_206, B_207, C_208) | ~r1_binop_1(A_206, B_207, C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_206, A_206), A_206))) | ~v1_funct_2(C_208, k2_zfmisc_1(A_206, A_206), A_206) | ~v1_funct_1(C_208) | ~m1_subset_1(B_207, A_206))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_77, plain, (![B_207]: (r3_binop_1('#skF_1', B_207, '#skF_5') | ~r2_binop_1('#skF_1', B_207, '#skF_5') | ~r1_binop_1('#skF_1', B_207, '#skF_5') | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1(B_207, '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_73])).
% 5.06/1.95  tff(c_95, plain, (![B_210]: (r3_binop_1('#skF_1', B_210, '#skF_5') | ~r2_binop_1('#skF_1', B_210, '#skF_5') | ~r1_binop_1('#skF_1', B_210, '#skF_5') | ~m1_subset_1(B_210, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_77])).
% 5.06/1.95  tff(c_56, plain, (r3_binop_1('#skF_2', '#skF_4', '#skF_6') | r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_59, plain, (r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_56])).
% 5.06/1.95  tff(c_48, plain, (~r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r3_binop_1('#skF_2', '#skF_4', '#skF_6') | ~r3_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_63, plain, (~r3_binop_1('#skF_2', '#skF_4', '#skF_6') | ~r3_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_48])).
% 5.06/1.95  tff(c_64, plain, (~r3_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_63])).
% 5.06/1.95  tff(c_102, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_5') | ~r1_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_95, c_64])).
% 5.06/1.95  tff(c_111, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_5') | ~r1_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 5.06/1.95  tff(c_112, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_111])).
% 5.06/1.95  tff(c_10, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k6_filter_1(A_9, B_10, C_11, D_12), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), k2_zfmisc_1(A_9, B_10)), k2_zfmisc_1(A_9, B_10)))) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_10, B_10), B_10))) | ~v1_funct_2(D_12, k2_zfmisc_1(B_10, B_10), B_10) | ~v1_funct_1(D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(C_11, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (v1_funct_2(k6_filter_1(A_9, B_10, C_11, D_12), k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), k2_zfmisc_1(A_9, B_10)), k2_zfmisc_1(A_9, B_10)) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_10, B_10), B_10))) | ~v1_funct_2(D_12, k2_zfmisc_1(B_10, B_10), B_10) | ~v1_funct_1(D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(C_11, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k1_domain_1(A_1, B_2, C_3, D_4), k2_zfmisc_1(A_1, B_2)) | ~m1_subset_1(D_4, B_2) | ~m1_subset_1(C_3, A_1) | v1_xboole_0(B_2) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.06/1.95  tff(c_113, plain, (![A_211, B_212, C_213, D_214]: (v1_funct_1(k6_filter_1(A_211, B_212, C_213, D_214)) | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_212, B_212), B_212))) | ~v1_funct_2(D_214, k2_zfmisc_1(B_212, B_212), B_212) | ~v1_funct_1(D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_211, A_211), A_211))) | ~v1_funct_2(C_213, k2_zfmisc_1(A_211, A_211), A_211) | ~v1_funct_1(C_213))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_115, plain, (![A_211, C_213]: (v1_funct_1(k6_filter_1(A_211, '#skF_2', C_213, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_211, A_211), A_211))) | ~v1_funct_2(C_213, k2_zfmisc_1(A_211, A_211), A_211) | ~v1_funct_1(C_213))), inference(resolution, [status(thm)], [c_28, c_113])).
% 5.06/1.95  tff(c_124, plain, (![A_215, C_216]: (v1_funct_1(k6_filter_1(A_215, '#skF_2', C_216, '#skF_6')) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_215, A_215), A_215))) | ~v1_funct_2(C_216, k2_zfmisc_1(A_215, A_215), A_215) | ~v1_funct_1(C_216))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_115])).
% 5.06/1.95  tff(c_130, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_124])).
% 5.06/1.95  tff(c_136, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_130])).
% 5.06/1.95  tff(c_65, plain, (![A_200, B_201, C_202]: (r1_binop_1(A_200, B_201, C_202) | ~r3_binop_1(A_200, B_201, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_200, A_200), A_200))) | ~v1_funct_2(C_202, k2_zfmisc_1(A_200, A_200), A_200) | ~v1_funct_1(C_202) | ~m1_subset_1(B_201, A_200))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_68, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_65])).
% 5.06/1.95  tff(c_171, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_68])).
% 5.06/1.95  tff(c_172, plain, (~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_171])).
% 5.06/1.95  tff(c_175, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_172])).
% 5.06/1.95  tff(c_178, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_175])).
% 5.06/1.95  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_178])).
% 5.06/1.95  tff(c_182, plain, (m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_171])).
% 5.06/1.95  tff(c_69, plain, (![A_203, B_204, C_205]: (r2_binop_1(A_203, B_204, C_205) | ~r3_binop_1(A_203, B_204, C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_203, A_203), A_203))) | ~v1_funct_2(C_205, k2_zfmisc_1(A_203, A_203), A_203) | ~v1_funct_1(C_205) | ~m1_subset_1(B_204, A_203))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_72, plain, (r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_69])).
% 5.06/1.95  tff(c_184, plain, (r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_136, c_72])).
% 5.06/1.95  tff(c_185, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_184])).
% 5.06/1.95  tff(c_188, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_185])).
% 5.06/1.95  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_188])).
% 5.06/1.95  tff(c_193, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_184])).
% 5.06/1.95  tff(c_195, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_193])).
% 5.06/1.95  tff(c_198, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_195])).
% 5.06/1.95  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_198])).
% 5.06/1.95  tff(c_204, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_193])).
% 5.06/1.95  tff(c_194, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_184])).
% 5.06/1.95  tff(c_181, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_171])).
% 5.06/1.95  tff(c_317, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_194, c_181])).
% 5.06/1.95  tff(c_20, plain, (![F_75, E_73, A_13, C_61, B_45, D_69]: (r1_binop_1(A_13, C_61, E_73) | ~r1_binop_1(k2_zfmisc_1(A_13, B_45), k1_domain_1(A_13, B_45, C_61, D_69), k6_filter_1(A_13, B_45, E_73, F_75)) | ~m1_subset_1(F_75, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45, B_45), B_45))) | ~v1_funct_2(F_75, k2_zfmisc_1(B_45, B_45), B_45) | ~v1_funct_1(F_75) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13, A_13), A_13))) | ~v1_funct_2(E_73, k2_zfmisc_1(A_13, A_13), A_13) | ~v1_funct_1(E_73) | ~m1_subset_1(D_69, B_45) | ~m1_subset_1(C_61, A_13) | v1_xboole_0(B_45) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.06/1.95  tff(c_323, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_317, c_20])).
% 5.06/1.95  tff(c_330, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_5') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_323])).
% 5.06/1.95  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_112, c_330])).
% 5.06/1.95  tff(c_333, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 5.06/1.95  tff(c_335, plain, (![A_274, B_275, C_276, D_277]: (v1_funct_1(k6_filter_1(A_274, B_275, C_276, D_277)) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_275, B_275), B_275))) | ~v1_funct_2(D_277, k2_zfmisc_1(B_275, B_275), B_275) | ~v1_funct_1(D_277) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_274, A_274), A_274))) | ~v1_funct_2(C_276, k2_zfmisc_1(A_274, A_274), A_274) | ~v1_funct_1(C_276))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_337, plain, (![A_274, C_276]: (v1_funct_1(k6_filter_1(A_274, '#skF_2', C_276, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_274, A_274), A_274))) | ~v1_funct_2(C_276, k2_zfmisc_1(A_274, A_274), A_274) | ~v1_funct_1(C_276))), inference(resolution, [status(thm)], [c_28, c_335])).
% 5.06/1.95  tff(c_346, plain, (![A_278, C_279]: (v1_funct_1(k6_filter_1(A_278, '#skF_2', C_279, '#skF_6')) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_278, A_278), A_278))) | ~v1_funct_2(C_279, k2_zfmisc_1(A_278, A_278), A_278) | ~v1_funct_1(C_279))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_337])).
% 5.06/1.95  tff(c_352, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_346])).
% 5.06/1.95  tff(c_358, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_352])).
% 5.06/1.95  tff(c_393, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_68])).
% 5.06/1.95  tff(c_394, plain, (~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_393])).
% 5.06/1.95  tff(c_397, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_394])).
% 5.06/1.95  tff(c_400, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_397])).
% 5.06/1.95  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_400])).
% 5.06/1.95  tff(c_404, plain, (m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_393])).
% 5.06/1.95  tff(c_406, plain, (r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_358, c_72])).
% 5.06/1.95  tff(c_407, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_406])).
% 5.06/1.95  tff(c_410, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_407])).
% 5.06/1.95  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_410])).
% 5.06/1.95  tff(c_415, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_406])).
% 5.06/1.95  tff(c_417, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_415])).
% 5.06/1.95  tff(c_420, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_417])).
% 5.06/1.95  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_420])).
% 5.06/1.95  tff(c_425, plain, (r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_415])).
% 5.06/1.95  tff(c_26, plain, (![A_76, F_138, B_108, D_132, E_136, C_124]: (r2_binop_1(A_76, C_124, E_136) | ~r2_binop_1(k2_zfmisc_1(A_76, B_108), k1_domain_1(A_76, B_108, C_124, D_132), k6_filter_1(A_76, B_108, E_136, F_138)) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108, B_108), B_108))) | ~v1_funct_2(F_138, k2_zfmisc_1(B_108, B_108), B_108) | ~v1_funct_1(F_138) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76, A_76), A_76))) | ~v1_funct_2(E_136, k2_zfmisc_1(A_76, A_76), A_76) | ~v1_funct_1(E_136) | ~m1_subset_1(D_132, B_108) | ~m1_subset_1(C_124, A_76) | v1_xboole_0(B_108) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.06/1.95  tff(c_432, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_425, c_26])).
% 5.06/1.95  tff(c_439, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_5') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_432])).
% 5.06/1.95  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_333, c_439])).
% 5.06/1.95  tff(c_442, plain, (~r3_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_63])).
% 5.06/1.95  tff(c_504, plain, (~r2_binop_1('#skF_2', '#skF_4', '#skF_6') | ~r1_binop_1('#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_497, c_442])).
% 5.06/1.95  tff(c_513, plain, (~r2_binop_1('#skF_2', '#skF_4', '#skF_6') | ~r1_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_504])).
% 5.06/1.95  tff(c_514, plain, (~r1_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_513])).
% 5.06/1.95  tff(c_486, plain, (![A_323, B_324, C_325, D_326]: (v1_funct_1(k6_filter_1(A_323, B_324, C_325, D_326)) | ~m1_subset_1(D_326, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_324, B_324), B_324))) | ~v1_funct_2(D_326, k2_zfmisc_1(B_324, B_324), B_324) | ~v1_funct_1(D_326) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_323, A_323), A_323))) | ~v1_funct_2(C_325, k2_zfmisc_1(A_323, A_323), A_323) | ~v1_funct_1(C_325))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_488, plain, (![A_323, C_325]: (v1_funct_1(k6_filter_1(A_323, '#skF_2', C_325, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_323, A_323), A_323))) | ~v1_funct_2(C_325, k2_zfmisc_1(A_323, A_323), A_323) | ~v1_funct_1(C_325))), inference(resolution, [status(thm)], [c_28, c_486])).
% 5.06/1.95  tff(c_539, plain, (![A_331, C_332]: (v1_funct_1(k6_filter_1(A_331, '#skF_2', C_332, '#skF_6')) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_331, A_331), A_331))) | ~v1_funct_2(C_332, k2_zfmisc_1(A_331, A_331), A_331) | ~v1_funct_1(C_332))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_488])).
% 5.06/1.95  tff(c_545, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_539])).
% 5.06/1.95  tff(c_551, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_545])).
% 5.06/1.95  tff(c_444, plain, (![A_314, B_315, C_316]: (r2_binop_1(A_314, B_315, C_316) | ~r3_binop_1(A_314, B_315, C_316) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_314, A_314), A_314))) | ~v1_funct_2(C_316, k2_zfmisc_1(A_314, A_314), A_314) | ~v1_funct_1(C_316) | ~m1_subset_1(B_315, A_314))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_452, plain, (r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_444])).
% 5.06/1.95  tff(c_453, plain, (~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_452])).
% 5.06/1.95  tff(c_456, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_453])).
% 5.06/1.95  tff(c_459, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_456])).
% 5.06/1.95  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_459])).
% 5.06/1.95  tff(c_462, plain, (~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_452])).
% 5.06/1.95  tff(c_569, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_462])).
% 5.06/1.95  tff(c_570, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_569])).
% 5.06/1.95  tff(c_585, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_570])).
% 5.06/1.95  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_585])).
% 5.06/1.95  tff(c_591, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_569])).
% 5.06/1.95  tff(c_493, plain, (![A_323, C_325]: (v1_funct_1(k6_filter_1(A_323, '#skF_2', C_325, '#skF_6')) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_323, A_323), A_323))) | ~v1_funct_2(C_325, k2_zfmisc_1(A_323, A_323), A_323) | ~v1_funct_1(C_325))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_488])).
% 5.06/1.95  tff(c_594, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_2', k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), '#skF_6')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_591, c_493])).
% 5.06/1.95  tff(c_604, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_2', k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), '#skF_6')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_594])).
% 5.06/1.95  tff(c_614, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_604])).
% 5.06/1.95  tff(c_618, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_614])).
% 5.06/1.95  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_618])).
% 5.06/1.95  tff(c_624, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_604])).
% 5.06/1.95  tff(c_463, plain, (m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_452])).
% 5.06/1.95  tff(c_464, plain, (![A_317, B_318, C_319]: (r1_binop_1(A_317, B_318, C_319) | ~r3_binop_1(A_317, B_318, C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_317, A_317), A_317))) | ~v1_funct_2(C_319, k2_zfmisc_1(A_317, A_317), A_317) | ~v1_funct_1(C_319) | ~m1_subset_1(B_318, A_317))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_468, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_464])).
% 5.06/1.95  tff(c_474, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_468])).
% 5.06/1.95  tff(c_626, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_624, c_591, c_474])).
% 5.06/1.95  tff(c_883, plain, (![C_396, B_399, F_397, E_400, D_401, A_398]: (r1_binop_1(B_399, D_401, F_397) | ~r1_binop_1(k2_zfmisc_1(A_398, B_399), k1_domain_1(A_398, B_399, C_396, D_401), k6_filter_1(A_398, B_399, E_400, F_397)) | ~m1_subset_1(F_397, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_399, B_399), B_399))) | ~v1_funct_2(F_397, k2_zfmisc_1(B_399, B_399), B_399) | ~v1_funct_1(F_397) | ~m1_subset_1(E_400, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_398, A_398), A_398))) | ~v1_funct_2(E_400, k2_zfmisc_1(A_398, A_398), A_398) | ~v1_funct_1(E_400) | ~m1_subset_1(D_401, B_399) | ~m1_subset_1(C_396, A_398) | v1_xboole_0(B_399) | v1_xboole_0(A_398))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.06/1.95  tff(c_886, plain, (r1_binop_1('#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_626, c_883])).
% 5.06/1.95  tff(c_889, plain, (r1_binop_1('#skF_2', '#skF_4', '#skF_6') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_886])).
% 5.06/1.95  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_514, c_889])).
% 5.06/1.95  tff(c_892, plain, (~r2_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_513])).
% 5.06/1.95  tff(c_905, plain, (![A_403, C_404]: (v1_funct_1(k6_filter_1(A_403, '#skF_2', C_404, '#skF_6')) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_403, A_403), A_403))) | ~v1_funct_2(C_404, k2_zfmisc_1(A_403, A_403), A_403) | ~v1_funct_1(C_404))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_488])).
% 5.06/1.95  tff(c_911, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_905])).
% 5.06/1.95  tff(c_917, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_911])).
% 5.06/1.95  tff(c_948, plain, (r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_474])).
% 5.06/1.95  tff(c_949, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_948])).
% 5.06/1.95  tff(c_952, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_949])).
% 5.06/1.95  tff(c_956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_952])).
% 5.06/1.95  tff(c_958, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_948])).
% 5.06/1.95  tff(c_960, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_462])).
% 5.06/1.95  tff(c_961, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_960])).
% 5.06/1.95  tff(c_964, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_961])).
% 5.06/1.95  tff(c_968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_964])).
% 5.06/1.95  tff(c_969, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_960])).
% 5.06/1.95  tff(c_1018, plain, (r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_969])).
% 5.06/1.95  tff(c_1055, plain, (![D_439, A_440, C_441, B_437, F_436, E_438]: (r2_binop_1(B_437, D_439, F_436) | ~r2_binop_1(k2_zfmisc_1(A_440, B_437), k1_domain_1(A_440, B_437, C_441, D_439), k6_filter_1(A_440, B_437, E_438, F_436)) | ~m1_subset_1(F_436, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_437, B_437), B_437))) | ~v1_funct_2(F_436, k2_zfmisc_1(B_437, B_437), B_437) | ~v1_funct_1(F_436) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_440, A_440), A_440))) | ~v1_funct_2(E_438, k2_zfmisc_1(A_440, A_440), A_440) | ~v1_funct_1(E_438) | ~m1_subset_1(D_439, B_437) | ~m1_subset_1(C_441, A_440) | v1_xboole_0(B_437) | v1_xboole_0(A_440))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.06/1.95  tff(c_1058, plain, (r2_binop_1('#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1018, c_1055])).
% 5.06/1.95  tff(c_1061, plain, (r2_binop_1('#skF_2', '#skF_4', '#skF_6') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_1058])).
% 5.06/1.95  tff(c_1063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_892, c_1061])).
% 5.06/1.95  tff(c_1065, plain, (~r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 5.06/1.95  tff(c_58, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_5') | r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.06/1.95  tff(c_1066, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1065, c_58])).
% 5.06/1.95  tff(c_1081, plain, (![A_449, B_450, C_451]: (r1_binop_1(A_449, B_450, C_451) | ~r3_binop_1(A_449, B_450, C_451) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_449, A_449), A_449))) | ~v1_funct_2(C_451, k2_zfmisc_1(A_449, A_449), A_449) | ~v1_funct_1(C_451) | ~m1_subset_1(B_450, A_449))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_1083, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1066, c_1081])).
% 5.06/1.95  tff(c_1088, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_34, c_1083])).
% 5.06/1.95  tff(c_1064, plain, (r3_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 5.06/1.95  tff(c_1085, plain, (r1_binop_1('#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1064, c_1081])).
% 5.06/1.95  tff(c_1091, plain, (r1_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_30, c_28, c_1085])).
% 5.06/1.95  tff(c_16, plain, (![F_75, E_73, A_13, C_61, B_45, D_69]: (r1_binop_1(k2_zfmisc_1(A_13, B_45), k1_domain_1(A_13, B_45, C_61, D_69), k6_filter_1(A_13, B_45, E_73, F_75)) | ~r1_binop_1(B_45, D_69, F_75) | ~r1_binop_1(A_13, C_61, E_73) | ~m1_subset_1(F_75, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45, B_45), B_45))) | ~v1_funct_2(F_75, k2_zfmisc_1(B_45, B_45), B_45) | ~v1_funct_1(F_75) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13, A_13), A_13))) | ~v1_funct_2(E_73, k2_zfmisc_1(A_13, A_13), A_13) | ~v1_funct_1(E_73) | ~m1_subset_1(D_69, B_45) | ~m1_subset_1(C_61, A_13) | v1_xboole_0(B_45) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.06/1.95  tff(c_1070, plain, (![A_446, B_447, C_448]: (r2_binop_1(A_446, B_447, C_448) | ~r3_binop_1(A_446, B_447, C_448) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_446, A_446), A_446))) | ~v1_funct_2(C_448, k2_zfmisc_1(A_446, A_446), A_446) | ~v1_funct_1(C_448) | ~m1_subset_1(B_447, A_446))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_1072, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1066, c_1070])).
% 5.06/1.95  tff(c_1077, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_34, c_1072])).
% 5.06/1.95  tff(c_1074, plain, (r2_binop_1('#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1064, c_1070])).
% 5.06/1.95  tff(c_1080, plain, (r2_binop_1('#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_30, c_28, c_1074])).
% 5.06/1.95  tff(c_22, plain, (![A_76, F_138, B_108, D_132, E_136, C_124]: (r2_binop_1(k2_zfmisc_1(A_76, B_108), k1_domain_1(A_76, B_108, C_124, D_132), k6_filter_1(A_76, B_108, E_136, F_138)) | ~r2_binop_1(B_108, D_132, F_138) | ~r2_binop_1(A_76, C_124, E_136) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108, B_108), B_108))) | ~v1_funct_2(F_138, k2_zfmisc_1(B_108, B_108), B_108) | ~v1_funct_1(F_138) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76, A_76), A_76))) | ~v1_funct_2(E_136, k2_zfmisc_1(A_76, A_76), A_76) | ~v1_funct_1(E_136) | ~m1_subset_1(D_132, B_108) | ~m1_subset_1(C_124, A_76) | v1_xboole_0(B_108) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.06/1.95  tff(c_1125, plain, (![A_457, B_458, C_459, D_460]: (v1_funct_1(k6_filter_1(A_457, B_458, C_459, D_460)) | ~m1_subset_1(D_460, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_458, B_458), B_458))) | ~v1_funct_2(D_460, k2_zfmisc_1(B_458, B_458), B_458) | ~v1_funct_1(D_460) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_457, A_457), A_457))) | ~v1_funct_2(C_459, k2_zfmisc_1(A_457, A_457), A_457) | ~v1_funct_1(C_459))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_1127, plain, (![A_457, C_459]: (v1_funct_1(k6_filter_1(A_457, '#skF_2', C_459, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_457, A_457), A_457))) | ~v1_funct_2(C_459, k2_zfmisc_1(A_457, A_457), A_457) | ~v1_funct_1(C_459))), inference(resolution, [status(thm)], [c_28, c_1125])).
% 5.06/1.95  tff(c_1136, plain, (![A_461, C_462]: (v1_funct_1(k6_filter_1(A_461, '#skF_2', C_462, '#skF_6')) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_461, A_461), A_461))) | ~v1_funct_2(C_462, k2_zfmisc_1(A_461, A_461), A_461) | ~v1_funct_1(C_462))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1127])).
% 5.06/1.95  tff(c_1142, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_1136])).
% 5.06/1.95  tff(c_1148, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1142])).
% 5.06/1.95  tff(c_1163, plain, (![A_469, B_470, C_471, D_472]: (m1_subset_1(k6_filter_1(A_469, B_470, C_471, D_472), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_469, B_470), k2_zfmisc_1(A_469, B_470)), k2_zfmisc_1(A_469, B_470)))) | ~m1_subset_1(D_472, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_470, B_470), B_470))) | ~v1_funct_2(D_472, k2_zfmisc_1(B_470, B_470), B_470) | ~v1_funct_1(D_472) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_469, A_469), A_469))) | ~v1_funct_2(C_471, k2_zfmisc_1(A_469, A_469), A_469) | ~v1_funct_1(C_471))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.95  tff(c_4, plain, (![A_5, B_6, C_8]: (r3_binop_1(A_5, B_6, C_8) | ~r2_binop_1(A_5, B_6, C_8) | ~r1_binop_1(A_5, B_6, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5, A_5), A_5))) | ~v1_funct_2(C_8, k2_zfmisc_1(A_5, A_5), A_5) | ~v1_funct_1(C_8) | ~m1_subset_1(B_6, A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.95  tff(c_1338, plain, (![D_552, B_551, B_553, A_550, C_549]: (r3_binop_1(k2_zfmisc_1(A_550, B_553), B_551, k6_filter_1(A_550, B_553, C_549, D_552)) | ~r2_binop_1(k2_zfmisc_1(A_550, B_553), B_551, k6_filter_1(A_550, B_553, C_549, D_552)) | ~r1_binop_1(k2_zfmisc_1(A_550, B_553), B_551, k6_filter_1(A_550, B_553, C_549, D_552)) | ~v1_funct_2(k6_filter_1(A_550, B_553, C_549, D_552), k2_zfmisc_1(k2_zfmisc_1(A_550, B_553), k2_zfmisc_1(A_550, B_553)), k2_zfmisc_1(A_550, B_553)) | ~v1_funct_1(k6_filter_1(A_550, B_553, C_549, D_552)) | ~m1_subset_1(B_551, k2_zfmisc_1(A_550, B_553)) | ~m1_subset_1(D_552, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_553, B_553), B_553))) | ~v1_funct_2(D_552, k2_zfmisc_1(B_553, B_553), B_553) | ~v1_funct_1(D_552) | ~m1_subset_1(C_549, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_550, A_550), A_550))) | ~v1_funct_2(C_549, k2_zfmisc_1(A_550, A_550), A_550) | ~v1_funct_1(C_549))), inference(resolution, [status(thm)], [c_1163, c_4])).
% 5.06/1.95  tff(c_1407, plain, (![B_568, C_565, A_567, B_564, D_566]: (r3_binop_1(k2_zfmisc_1(A_567, B_564), B_568, k6_filter_1(A_567, B_564, C_565, D_566)) | ~r2_binop_1(k2_zfmisc_1(A_567, B_564), B_568, k6_filter_1(A_567, B_564, C_565, D_566)) | ~r1_binop_1(k2_zfmisc_1(A_567, B_564), B_568, k6_filter_1(A_567, B_564, C_565, D_566)) | ~v1_funct_1(k6_filter_1(A_567, B_564, C_565, D_566)) | ~m1_subset_1(B_568, k2_zfmisc_1(A_567, B_564)) | ~m1_subset_1(D_566, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_564, B_564), B_564))) | ~v1_funct_2(D_566, k2_zfmisc_1(B_564, B_564), B_564) | ~v1_funct_1(D_566) | ~m1_subset_1(C_565, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_567, A_567), A_567))) | ~v1_funct_2(C_565, k2_zfmisc_1(A_567, A_567), A_567) | ~v1_funct_1(C_565))), inference(resolution, [status(thm)], [c_12, c_1338])).
% 5.06/1.95  tff(c_1411, plain, (![A_567, B_568, C_565]: (r3_binop_1(k2_zfmisc_1(A_567, '#skF_2'), B_568, k6_filter_1(A_567, '#skF_2', C_565, '#skF_6')) | ~r2_binop_1(k2_zfmisc_1(A_567, '#skF_2'), B_568, k6_filter_1(A_567, '#skF_2', C_565, '#skF_6')) | ~r1_binop_1(k2_zfmisc_1(A_567, '#skF_2'), B_568, k6_filter_1(A_567, '#skF_2', C_565, '#skF_6')) | ~v1_funct_1(k6_filter_1(A_567, '#skF_2', C_565, '#skF_6')) | ~m1_subset_1(B_568, k2_zfmisc_1(A_567, '#skF_2')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_565, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_567, A_567), A_567))) | ~v1_funct_2(C_565, k2_zfmisc_1(A_567, A_567), A_567) | ~v1_funct_1(C_565))), inference(resolution, [status(thm)], [c_28, c_1407])).
% 5.06/1.95  tff(c_1474, plain, (![A_576, B_577, C_578]: (r3_binop_1(k2_zfmisc_1(A_576, '#skF_2'), B_577, k6_filter_1(A_576, '#skF_2', C_578, '#skF_6')) | ~r2_binop_1(k2_zfmisc_1(A_576, '#skF_2'), B_577, k6_filter_1(A_576, '#skF_2', C_578, '#skF_6')) | ~r1_binop_1(k2_zfmisc_1(A_576, '#skF_2'), B_577, k6_filter_1(A_576, '#skF_2', C_578, '#skF_6')) | ~v1_funct_1(k6_filter_1(A_576, '#skF_2', C_578, '#skF_6')) | ~m1_subset_1(B_577, k2_zfmisc_1(A_576, '#skF_2')) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_576, A_576), A_576))) | ~v1_funct_2(C_578, k2_zfmisc_1(A_576, A_576), A_576) | ~v1_funct_1(C_578))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1411])).
% 5.06/1.95  tff(c_1480, plain, (![B_577]: (r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), B_577, k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), B_577, k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), B_577, k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_577, k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_1474])).
% 5.06/1.95  tff(c_1503, plain, (![B_588]: (r3_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), B_588, k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), B_588, k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), B_588, k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_588, k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1148, c_1480])).
% 5.06/1.95  tff(c_1517, plain, (~r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1503, c_1065])).
% 5.06/1.95  tff(c_1518, plain, (~m1_subset_1(k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1517])).
% 5.06/1.95  tff(c_1521, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1518])).
% 5.06/1.95  tff(c_1524, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1521])).
% 5.06/1.95  tff(c_1526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_1524])).
% 5.06/1.95  tff(c_1527, plain, (~r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6')) | ~r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_1517])).
% 5.06/1.95  tff(c_1529, plain, (~r2_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1527])).
% 5.06/1.95  tff(c_1532, plain, (~r2_binop_1('#skF_2', '#skF_4', '#skF_6') | ~r2_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1529])).
% 5.06/1.95  tff(c_1535, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_1077, c_1080, c_1532])).
% 5.06/1.95  tff(c_1537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_1535])).
% 5.06/1.95  tff(c_1538, plain, (~r1_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k1_domain_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_filter_1('#skF_1', '#skF_2', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_1527])).
% 5.06/1.95  tff(c_1542, plain, (~r1_binop_1('#skF_2', '#skF_4', '#skF_6') | ~r1_binop_1('#skF_1', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1538])).
% 5.06/1.95  tff(c_1545, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_1088, c_1091, c_1542])).
% 5.06/1.95  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_1545])).
% 5.06/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.95  
% 5.06/1.95  Inference rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Ref     : 0
% 5.06/1.95  #Sup     : 249
% 5.06/1.95  #Fact    : 0
% 5.06/1.95  #Define  : 0
% 5.06/1.95  #Split   : 18
% 5.06/1.95  #Chain   : 0
% 5.06/1.95  #Close   : 0
% 5.06/1.95  
% 5.06/1.95  Ordering : KBO
% 5.06/1.95  
% 5.06/1.95  Simplification rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Subsume      : 7
% 5.06/1.95  #Demod        : 609
% 5.06/1.95  #Tautology    : 51
% 5.06/1.95  #SimpNegUnit  : 21
% 5.06/1.95  #BackRed      : 0
% 5.06/1.95  
% 5.06/1.95  #Partial instantiations: 0
% 5.06/1.95  #Strategies tried      : 1
% 5.06/1.95  
% 5.06/1.95  Timing (in seconds)
% 5.06/1.95  ----------------------
% 5.06/1.95  Preprocessing        : 0.39
% 5.06/1.95  Parsing              : 0.21
% 5.06/1.95  CNF conversion       : 0.05
% 5.06/1.95  Main loop            : 0.74
% 5.06/1.95  Inferencing          : 0.28
% 5.06/1.95  Reduction            : 0.23
% 5.06/1.95  Demodulation         : 0.16
% 5.06/1.95  BG Simplification    : 0.03
% 5.06/1.95  Subsumption          : 0.16
% 5.06/1.95  Abstraction          : 0.02
% 5.06/1.95  MUC search           : 0.00
% 5.06/1.95  Cooper               : 0.00
% 5.06/1.95  Total                : 1.20
% 5.06/1.95  Index Insertion      : 0.00
% 5.06/1.95  Index Deletion       : 0.00
% 5.06/1.95  Index Matching       : 0.00
% 5.06/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
