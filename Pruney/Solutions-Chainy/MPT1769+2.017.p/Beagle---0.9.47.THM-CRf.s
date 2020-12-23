%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:20 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 419 expanded)
%              Number of leaves         :   41 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  428 (3461 expanded)
%              Number of equality atoms :   49 ( 207 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_213,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_34,plain,(
    '#skF_6' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_38,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_85,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_450,plain,(
    ! [B_270,A_271,C_274,F_273,D_272] :
      ( r1_funct_2(A_271,B_270,C_274,D_272,F_273,F_273)
      | ~ m1_subset_1(F_273,k1_zfmisc_1(k2_zfmisc_1(C_274,D_272)))
      | ~ v1_funct_2(F_273,C_274,D_272)
      | ~ m1_subset_1(F_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_270)))
      | ~ v1_funct_2(F_273,A_271,B_270)
      | ~ v1_funct_1(F_273)
      | v1_xboole_0(D_272)
      | v1_xboole_0(B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_452,plain,(
    ! [A_271,B_270] :
      ( r1_funct_2(A_271,B_270,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_271,B_270)))
      | ~ v1_funct_2('#skF_9',A_271,B_270)
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_270) ) ),
    inference(resolution,[status(thm)],[c_86,c_450])).

tff(c_459,plain,(
    ! [A_271,B_270] :
      ( r1_funct_2(A_271,B_270,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_271,B_270)))
      | ~ v1_funct_2('#skF_9',A_271,B_270)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85,c_452])).

tff(c_466,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_207] :
      ( m1_subset_1('#skF_2'(A_207),k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_399,plain,(
    ! [A_256,A_257] :
      ( ~ v1_xboole_0(u1_struct_0(A_256))
      | ~ r2_hidden(A_257,'#skF_2'(A_256))
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_126,c_12])).

tff(c_410,plain,(
    ! [A_258,B_259] :
      ( ~ v1_xboole_0(u1_struct_0(A_258))
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258)
      | r1_tarski('#skF_2'(A_258),B_259) ) ),
    inference(resolution,[status(thm)],[c_6,c_399])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_415,plain,(
    ! [A_258] :
      ( '#skF_2'(A_258) = k1_xboole_0
      | ~ v1_xboole_0(u1_struct_0(A_258))
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_410,c_10])).

tff(c_475,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_466,c_415])).

tff(c_478,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_475])).

tff(c_479,plain,(
    '#skF_2'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_478])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0('#skF_2'(A_10))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_497,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_16])).

tff(c_516,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8,c_497])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_516])).

tff(c_520,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_50,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_32,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_87,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_526,plain,(
    ! [A_288,E_289,D_290,C_292,B_287,F_291] :
      ( F_291 = E_289
      | ~ r1_funct_2(A_288,B_287,C_292,D_290,E_289,F_291)
      | ~ m1_subset_1(F_291,k1_zfmisc_1(k2_zfmisc_1(C_292,D_290)))
      | ~ v1_funct_2(F_291,C_292,D_290)
      | ~ v1_funct_1(F_291)
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287)))
      | ~ v1_funct_2(E_289,A_288,B_287)
      | ~ v1_funct_1(E_289)
      | v1_xboole_0(D_290)
      | v1_xboole_0(B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_534,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_87,c_526])).

tff(c_552,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_40,c_85,c_86,c_534])).

tff(c_553,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_552])).

tff(c_206,plain,(
    ! [C_233,A_230,D_231,F_232,B_229] :
      ( r1_funct_2(A_230,B_229,C_233,D_231,F_232,F_232)
      | ~ m1_subset_1(F_232,k1_zfmisc_1(k2_zfmisc_1(C_233,D_231)))
      | ~ v1_funct_2(F_232,C_233,D_231)
      | ~ m1_subset_1(F_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_229)))
      | ~ v1_funct_2(F_232,A_230,B_229)
      | ~ v1_funct_1(F_232)
      | v1_xboole_0(D_231)
      | v1_xboole_0(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_208,plain,(
    ! [A_230,B_229] :
      ( r1_funct_2(A_230,B_229,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_230,B_229)))
      | ~ v1_funct_2('#skF_9',A_230,B_229)
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_229) ) ),
    inference(resolution,[status(thm)],[c_86,c_206])).

tff(c_215,plain,(
    ! [A_230,B_229] :
      ( r1_funct_2(A_230,B_229,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(A_230,B_229)))
      | ~ v1_funct_2('#skF_9',A_230,B_229)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85,c_208])).

tff(c_222,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_154,plain,(
    ! [A_215,A_216] :
      ( ~ v1_xboole_0(u1_struct_0(A_215))
      | ~ r2_hidden(A_216,'#skF_2'(A_215))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_126,c_12])).

tff(c_165,plain,(
    ! [A_217,B_218] :
      ( ~ v1_xboole_0(u1_struct_0(A_217))
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217)
      | r1_tarski('#skF_2'(A_217),B_218) ) ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_170,plain,(
    ! [A_217] :
      ( '#skF_2'(A_217) = k1_xboole_0
      | ~ v1_xboole_0(u1_struct_0(A_217))
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_165,c_10])).

tff(c_225,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_170])).

tff(c_228,plain,
    ( '#skF_2'('#skF_4') = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_225])).

tff(c_229,plain,(
    '#skF_2'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_228])).

tff(c_247,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_16])).

tff(c_266,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8,c_247])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_266])).

tff(c_270,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_272,plain,(
    ! [C_241,E_238,D_239,B_236,F_240,A_237] :
      ( F_240 = E_238
      | ~ r1_funct_2(A_237,B_236,C_241,D_239,E_238,F_240)
      | ~ m1_subset_1(F_240,k1_zfmisc_1(k2_zfmisc_1(C_241,D_239)))
      | ~ v1_funct_2(F_240,C_241,D_239)
      | ~ v1_funct_1(F_240)
      | ~ m1_subset_1(E_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236)))
      | ~ v1_funct_2(E_238,A_237,B_236)
      | ~ v1_funct_1(E_238)
      | v1_xboole_0(D_239)
      | v1_xboole_0(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_276,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_87,c_272])).

tff(c_284,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_40,c_85,c_86,c_276])).

tff(c_285,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_284])).

tff(c_74,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_84,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_74])).

tff(c_153,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_80,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_82,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_179,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_82])).

tff(c_286,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_179])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_83,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54])).

tff(c_339,plain,(
    ! [B_251,E_252,C_253,D_250,A_249] :
      ( k3_tmap_1(A_249,B_251,C_253,D_250,E_252) = k2_partfun1(u1_struct_0(C_253),u1_struct_0(B_251),E_252,u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,C_253)
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_253),u1_struct_0(B_251))))
      | ~ v1_funct_2(E_252,u1_struct_0(C_253),u1_struct_0(B_251))
      | ~ v1_funct_1(E_252)
      | ~ m1_pre_topc(D_250,A_249)
      | ~ m1_pre_topc(C_253,A_249)
      | ~ l1_pre_topc(B_251)
      | ~ v2_pre_topc(B_251)
      | v2_struct_0(B_251)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_341,plain,(
    ! [A_249,D_250] :
      ( k3_tmap_1(A_249,'#skF_4','#skF_3',D_250,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_250,A_249)
      | ~ m1_pre_topc('#skF_3',A_249)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_86,c_339])).

tff(c_346,plain,(
    ! [A_249,D_250] :
      ( k3_tmap_1(A_249,'#skF_4','#skF_3',D_250,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_3')
      | ~ m1_pre_topc(D_250,A_249)
      | ~ m1_pre_topc('#skF_3',A_249)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_40,c_85,c_341])).

tff(c_352,plain,(
    ! [A_254,D_255] :
      ( k3_tmap_1(A_254,'#skF_4','#skF_3',D_255,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_255))
      | ~ m1_pre_topc(D_255,'#skF_3')
      | ~ m1_pre_topc(D_255,A_254)
      | ~ m1_pre_topc('#skF_3',A_254)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254)
      | v2_struct_0(A_254) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_346])).

tff(c_358,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_352])).

tff(c_367,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_358])).

tff(c_368,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_367])).

tff(c_316,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k2_partfun1(u1_struct_0(A_244),u1_struct_0(B_245),C_246,u1_struct_0(D_247)) = k2_tmap_1(A_244,B_245,C_246,D_247)
      | ~ m1_pre_topc(D_247,A_244)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244),u1_struct_0(B_245))))
      | ~ v1_funct_2(C_246,u1_struct_0(A_244),u1_struct_0(B_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_318,plain,(
    ! [D_247] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_247)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_247)
      | ~ m1_pre_topc(D_247,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_86,c_316])).

tff(c_323,plain,(
    ! [D_247] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_247)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_247)
      | ~ m1_pre_topc(D_247,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_85,c_318])).

tff(c_324,plain,(
    ! [D_247] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_247)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_247)
      | ~ m1_pre_topc(D_247,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_323])).

tff(c_376,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_324])).

tff(c_383,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_376])).

tff(c_388,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_153])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_388])).

tff(c_392,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_555,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_392])).

tff(c_597,plain,(
    ! [E_301,C_302,D_299,A_298,B_300] :
      ( k3_tmap_1(A_298,B_300,C_302,D_299,E_301) = k2_partfun1(u1_struct_0(C_302),u1_struct_0(B_300),E_301,u1_struct_0(D_299))
      | ~ m1_pre_topc(D_299,C_302)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_302),u1_struct_0(B_300))))
      | ~ v1_funct_2(E_301,u1_struct_0(C_302),u1_struct_0(B_300))
      | ~ v1_funct_1(E_301)
      | ~ m1_pre_topc(D_299,A_298)
      | ~ m1_pre_topc(C_302,A_298)
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | v2_struct_0(B_300)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_599,plain,(
    ! [A_298,D_299] :
      ( k3_tmap_1(A_298,'#skF_4','#skF_3',D_299,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_299))
      | ~ m1_pre_topc(D_299,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_299,A_298)
      | ~ m1_pre_topc('#skF_3',A_298)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_86,c_597])).

tff(c_604,plain,(
    ! [A_298,D_299] :
      ( k3_tmap_1(A_298,'#skF_4','#skF_3',D_299,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_299))
      | ~ m1_pre_topc(D_299,'#skF_3')
      | ~ m1_pre_topc(D_299,A_298)
      | ~ m1_pre_topc('#skF_3',A_298)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_40,c_85,c_599])).

tff(c_610,plain,(
    ! [A_303,D_304] :
      ( k3_tmap_1(A_303,'#skF_4','#skF_3',D_304,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_304))
      | ~ m1_pre_topc(D_304,'#skF_3')
      | ~ m1_pre_topc(D_304,A_303)
      | ~ m1_pre_topc('#skF_3',A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_604])).

tff(c_616,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_610])).

tff(c_625,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_616])).

tff(c_626,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_625])).

tff(c_567,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k2_partfun1(u1_struct_0(A_293),u1_struct_0(B_294),C_295,u1_struct_0(D_296)) = k2_tmap_1(A_293,B_294,C_295,D_296)
      | ~ m1_pre_topc(D_296,A_293)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293),u1_struct_0(B_294))))
      | ~ v1_funct_2(C_295,u1_struct_0(A_293),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_569,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_296)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_296)
      | ~ m1_pre_topc(D_296,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_86,c_567])).

tff(c_574,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_296)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_296)
      | ~ m1_pre_topc(D_296,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_85,c_569])).

tff(c_575,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_296)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_296)
      | ~ m1_pre_topc(D_296,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_574])).

tff(c_634,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_575])).

tff(c_641,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_634])).

tff(c_394,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_394])).

tff(c_396,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_646,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_396])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.47  
% 3.31/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.47  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.31/1.47  
% 3.31/1.47  %Foreground sorts:
% 3.31/1.47  
% 3.31/1.47  
% 3.31/1.47  %Background operators:
% 3.31/1.47  
% 3.31/1.47  
% 3.31/1.47  %Foreground operators:
% 3.31/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.31/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.31/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.47  tff('#skF_9', type, '#skF_9': $i).
% 3.31/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.31/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.47  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.31/1.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.31/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.47  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.31/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.47  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.31/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.47  
% 3.31/1.49  tff(f_213, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 3.31/1.49  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.31/1.49  tff(f_81, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.31/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.49  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.31/1.49  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.31/1.49  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.31/1.49  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.31/1.49  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.31/1.49  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.49  tff(c_40, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_34, plain, ('#skF_6'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_38, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_85, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.31/1.49  tff(c_36, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_86, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 3.31/1.49  tff(c_450, plain, (![B_270, A_271, C_274, F_273, D_272]: (r1_funct_2(A_271, B_270, C_274, D_272, F_273, F_273) | ~m1_subset_1(F_273, k1_zfmisc_1(k2_zfmisc_1(C_274, D_272))) | ~v1_funct_2(F_273, C_274, D_272) | ~m1_subset_1(F_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))) | ~v1_funct_2(F_273, A_271, B_270) | ~v1_funct_1(F_273) | v1_xboole_0(D_272) | v1_xboole_0(B_270))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.49  tff(c_452, plain, (![A_271, B_270]: (r1_funct_2(A_271, B_270, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))) | ~v1_funct_2('#skF_9', A_271, B_270) | ~v1_funct_1('#skF_9') | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_270))), inference(resolution, [status(thm)], [c_86, c_450])).
% 3.31/1.49  tff(c_459, plain, (![A_271, B_270]: (r1_funct_2(A_271, B_270, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))) | ~v1_funct_2('#skF_9', A_271, B_270) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_270))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85, c_452])).
% 3.31/1.49  tff(c_466, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_459])).
% 3.31/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.49  tff(c_126, plain, (![A_207]: (m1_subset_1('#skF_2'(A_207), k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.31/1.49  tff(c_12, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.31/1.49  tff(c_399, plain, (![A_256, A_257]: (~v1_xboole_0(u1_struct_0(A_256)) | ~r2_hidden(A_257, '#skF_2'(A_256)) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(resolution, [status(thm)], [c_126, c_12])).
% 3.31/1.49  tff(c_410, plain, (![A_258, B_259]: (~v1_xboole_0(u1_struct_0(A_258)) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258) | r1_tarski('#skF_2'(A_258), B_259))), inference(resolution, [status(thm)], [c_6, c_399])).
% 3.31/1.49  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.49  tff(c_415, plain, (![A_258]: ('#skF_2'(A_258)=k1_xboole_0 | ~v1_xboole_0(u1_struct_0(A_258)) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(resolution, [status(thm)], [c_410, c_10])).
% 3.31/1.49  tff(c_475, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_466, c_415])).
% 3.31/1.49  tff(c_478, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_475])).
% 3.31/1.49  tff(c_479, plain, ('#skF_2'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_478])).
% 3.31/1.49  tff(c_16, plain, (![A_10]: (~v1_xboole_0('#skF_2'(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.31/1.49  tff(c_497, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_479, c_16])).
% 3.31/1.49  tff(c_516, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8, c_497])).
% 3.31/1.49  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_516])).
% 3.31/1.49  tff(c_520, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_459])).
% 3.31/1.49  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_50, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_32, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_87, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 3.31/1.49  tff(c_526, plain, (![A_288, E_289, D_290, C_292, B_287, F_291]: (F_291=E_289 | ~r1_funct_2(A_288, B_287, C_292, D_290, E_289, F_291) | ~m1_subset_1(F_291, k1_zfmisc_1(k2_zfmisc_1(C_292, D_290))) | ~v1_funct_2(F_291, C_292, D_290) | ~v1_funct_1(F_291) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))) | ~v1_funct_2(E_289, A_288, B_287) | ~v1_funct_1(E_289) | v1_xboole_0(D_290) | v1_xboole_0(B_287))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.49  tff(c_534, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_87, c_526])).
% 3.31/1.49  tff(c_552, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_40, c_85, c_86, c_534])).
% 3.31/1.49  tff(c_553, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_520, c_552])).
% 3.31/1.49  tff(c_206, plain, (![C_233, A_230, D_231, F_232, B_229]: (r1_funct_2(A_230, B_229, C_233, D_231, F_232, F_232) | ~m1_subset_1(F_232, k1_zfmisc_1(k2_zfmisc_1(C_233, D_231))) | ~v1_funct_2(F_232, C_233, D_231) | ~m1_subset_1(F_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))) | ~v1_funct_2(F_232, A_230, B_229) | ~v1_funct_1(F_232) | v1_xboole_0(D_231) | v1_xboole_0(B_229))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.49  tff(c_208, plain, (![A_230, B_229]: (r1_funct_2(A_230, B_229, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))) | ~v1_funct_2('#skF_9', A_230, B_229) | ~v1_funct_1('#skF_9') | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_229))), inference(resolution, [status(thm)], [c_86, c_206])).
% 3.31/1.49  tff(c_215, plain, (![A_230, B_229]: (r1_funct_2(A_230, B_229, u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))) | ~v1_funct_2('#skF_9', A_230, B_229) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_229))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85, c_208])).
% 3.31/1.49  tff(c_222, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_215])).
% 3.31/1.49  tff(c_154, plain, (![A_215, A_216]: (~v1_xboole_0(u1_struct_0(A_215)) | ~r2_hidden(A_216, '#skF_2'(A_215)) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_126, c_12])).
% 3.31/1.49  tff(c_165, plain, (![A_217, B_218]: (~v1_xboole_0(u1_struct_0(A_217)) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217) | r1_tarski('#skF_2'(A_217), B_218))), inference(resolution, [status(thm)], [c_6, c_154])).
% 3.31/1.49  tff(c_170, plain, (![A_217]: ('#skF_2'(A_217)=k1_xboole_0 | ~v1_xboole_0(u1_struct_0(A_217)) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_165, c_10])).
% 3.31/1.49  tff(c_225, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_222, c_170])).
% 3.31/1.49  tff(c_228, plain, ('#skF_2'('#skF_4')=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_225])).
% 3.31/1.49  tff(c_229, plain, ('#skF_2'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_228])).
% 3.31/1.49  tff(c_247, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_229, c_16])).
% 3.31/1.49  tff(c_266, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8, c_247])).
% 3.31/1.49  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_266])).
% 3.31/1.49  tff(c_270, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_215])).
% 3.31/1.49  tff(c_272, plain, (![C_241, E_238, D_239, B_236, F_240, A_237]: (F_240=E_238 | ~r1_funct_2(A_237, B_236, C_241, D_239, E_238, F_240) | ~m1_subset_1(F_240, k1_zfmisc_1(k2_zfmisc_1(C_241, D_239))) | ~v1_funct_2(F_240, C_241, D_239) | ~v1_funct_1(F_240) | ~m1_subset_1(E_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))) | ~v1_funct_2(E_238, A_237, B_236) | ~v1_funct_1(E_238) | v1_xboole_0(D_239) | v1_xboole_0(B_236))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.49  tff(c_276, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_87, c_272])).
% 3.31/1.49  tff(c_284, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_40, c_85, c_86, c_276])).
% 3.31/1.49  tff(c_285, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_270, c_284])).
% 3.31/1.49  tff(c_74, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_84, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_74])).
% 3.31/1.49  tff(c_153, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 3.31/1.49  tff(c_80, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_82, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 3.31/1.49  tff(c_179, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_153, c_82])).
% 3.31/1.49  tff(c_286, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_179])).
% 3.31/1.49  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.31/1.49  tff(c_83, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54])).
% 3.31/1.49  tff(c_339, plain, (![B_251, E_252, C_253, D_250, A_249]: (k3_tmap_1(A_249, B_251, C_253, D_250, E_252)=k2_partfun1(u1_struct_0(C_253), u1_struct_0(B_251), E_252, u1_struct_0(D_250)) | ~m1_pre_topc(D_250, C_253) | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_253), u1_struct_0(B_251)))) | ~v1_funct_2(E_252, u1_struct_0(C_253), u1_struct_0(B_251)) | ~v1_funct_1(E_252) | ~m1_pre_topc(D_250, A_249) | ~m1_pre_topc(C_253, A_249) | ~l1_pre_topc(B_251) | ~v2_pre_topc(B_251) | v2_struct_0(B_251) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.31/1.49  tff(c_341, plain, (![A_249, D_250]: (k3_tmap_1(A_249, '#skF_4', '#skF_3', D_250, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_250, A_249) | ~m1_pre_topc('#skF_3', A_249) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(resolution, [status(thm)], [c_86, c_339])).
% 3.31/1.49  tff(c_346, plain, (![A_249, D_250]: (k3_tmap_1(A_249, '#skF_4', '#skF_3', D_250, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_3') | ~m1_pre_topc(D_250, A_249) | ~m1_pre_topc('#skF_3', A_249) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_40, c_85, c_341])).
% 3.31/1.49  tff(c_352, plain, (![A_254, D_255]: (k3_tmap_1(A_254, '#skF_4', '#skF_3', D_255, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_255)) | ~m1_pre_topc(D_255, '#skF_3') | ~m1_pre_topc(D_255, A_254) | ~m1_pre_topc('#skF_3', A_254) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254) | v2_struct_0(A_254))), inference(negUnitSimplification, [status(thm)], [c_66, c_346])).
% 3.31/1.49  tff(c_358, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_352])).
% 3.31/1.49  tff(c_367, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_358])).
% 3.31/1.49  tff(c_368, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_367])).
% 3.31/1.49  tff(c_316, plain, (![A_244, B_245, C_246, D_247]: (k2_partfun1(u1_struct_0(A_244), u1_struct_0(B_245), C_246, u1_struct_0(D_247))=k2_tmap_1(A_244, B_245, C_246, D_247) | ~m1_pre_topc(D_247, A_244) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244), u1_struct_0(B_245)))) | ~v1_funct_2(C_246, u1_struct_0(A_244), u1_struct_0(B_245)) | ~v1_funct_1(C_246) | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.49  tff(c_318, plain, (![D_247]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_247))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_247) | ~m1_pre_topc(D_247, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_316])).
% 3.31/1.49  tff(c_323, plain, (![D_247]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_247))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_247) | ~m1_pre_topc(D_247, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_85, c_318])).
% 3.31/1.49  tff(c_324, plain, (![D_247]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_247))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_247) | ~m1_pre_topc(D_247, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_323])).
% 3.31/1.49  tff(c_376, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_368, c_324])).
% 3.31/1.49  tff(c_383, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_376])).
% 3.31/1.49  tff(c_388, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_153])).
% 3.31/1.49  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_388])).
% 3.31/1.49  tff(c_392, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 3.31/1.49  tff(c_555, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_392])).
% 3.31/1.49  tff(c_597, plain, (![E_301, C_302, D_299, A_298, B_300]: (k3_tmap_1(A_298, B_300, C_302, D_299, E_301)=k2_partfun1(u1_struct_0(C_302), u1_struct_0(B_300), E_301, u1_struct_0(D_299)) | ~m1_pre_topc(D_299, C_302) | ~m1_subset_1(E_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_302), u1_struct_0(B_300)))) | ~v1_funct_2(E_301, u1_struct_0(C_302), u1_struct_0(B_300)) | ~v1_funct_1(E_301) | ~m1_pre_topc(D_299, A_298) | ~m1_pre_topc(C_302, A_298) | ~l1_pre_topc(B_300) | ~v2_pre_topc(B_300) | v2_struct_0(B_300) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.31/1.49  tff(c_599, plain, (![A_298, D_299]: (k3_tmap_1(A_298, '#skF_4', '#skF_3', D_299, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_299)) | ~m1_pre_topc(D_299, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_299, A_298) | ~m1_pre_topc('#skF_3', A_298) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(resolution, [status(thm)], [c_86, c_597])).
% 3.31/1.49  tff(c_604, plain, (![A_298, D_299]: (k3_tmap_1(A_298, '#skF_4', '#skF_3', D_299, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_299)) | ~m1_pre_topc(D_299, '#skF_3') | ~m1_pre_topc(D_299, A_298) | ~m1_pre_topc('#skF_3', A_298) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_40, c_85, c_599])).
% 3.31/1.49  tff(c_610, plain, (![A_303, D_304]: (k3_tmap_1(A_303, '#skF_4', '#skF_3', D_304, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_304)) | ~m1_pre_topc(D_304, '#skF_3') | ~m1_pre_topc(D_304, A_303) | ~m1_pre_topc('#skF_3', A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(negUnitSimplification, [status(thm)], [c_66, c_604])).
% 3.31/1.49  tff(c_616, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_610])).
% 3.31/1.49  tff(c_625, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_616])).
% 3.31/1.49  tff(c_626, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_625])).
% 3.31/1.49  tff(c_567, plain, (![A_293, B_294, C_295, D_296]: (k2_partfun1(u1_struct_0(A_293), u1_struct_0(B_294), C_295, u1_struct_0(D_296))=k2_tmap_1(A_293, B_294, C_295, D_296) | ~m1_pre_topc(D_296, A_293) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293), u1_struct_0(B_294)))) | ~v1_funct_2(C_295, u1_struct_0(A_293), u1_struct_0(B_294)) | ~v1_funct_1(C_295) | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.49  tff(c_569, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_296))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_296) | ~m1_pre_topc(D_296, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_567])).
% 3.31/1.49  tff(c_574, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_296))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_296) | ~m1_pre_topc(D_296, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_85, c_569])).
% 3.31/1.49  tff(c_575, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_296))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_296) | ~m1_pre_topc(D_296, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_574])).
% 3.31/1.49  tff(c_634, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_626, c_575])).
% 3.31/1.49  tff(c_641, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_634])).
% 3.31/1.49  tff(c_394, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_82])).
% 3.31/1.49  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_392, c_394])).
% 3.31/1.49  tff(c_396, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 3.31/1.49  tff(c_646, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_396])).
% 3.31/1.49  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_646])).
% 3.31/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.49  
% 3.31/1.49  Inference rules
% 3.31/1.49  ----------------------
% 3.31/1.49  #Ref     : 0
% 3.31/1.49  #Sup     : 103
% 3.31/1.49  #Fact    : 0
% 3.31/1.49  #Define  : 0
% 3.31/1.49  #Split   : 8
% 3.31/1.49  #Chain   : 0
% 3.31/1.49  #Close   : 0
% 3.31/1.49  
% 3.31/1.49  Ordering : KBO
% 3.31/1.49  
% 3.31/1.49  Simplification rules
% 3.31/1.49  ----------------------
% 3.31/1.49  #Subsume      : 17
% 3.31/1.49  #Demod        : 194
% 3.31/1.49  #Tautology    : 40
% 3.31/1.49  #SimpNegUnit  : 42
% 3.31/1.49  #BackRed      : 15
% 3.31/1.49  
% 3.31/1.49  #Partial instantiations: 0
% 3.31/1.49  #Strategies tried      : 1
% 3.31/1.49  
% 3.31/1.49  Timing (in seconds)
% 3.31/1.49  ----------------------
% 3.31/1.49  Preprocessing        : 0.37
% 3.31/1.49  Parsing              : 0.19
% 3.31/1.49  CNF conversion       : 0.05
% 3.31/1.49  Main loop            : 0.34
% 3.31/1.49  Inferencing          : 0.11
% 3.31/1.49  Reduction            : 0.12
% 3.31/1.49  Demodulation         : 0.09
% 3.31/1.49  BG Simplification    : 0.02
% 3.31/1.49  Subsumption          : 0.06
% 3.31/1.49  Abstraction          : 0.02
% 3.31/1.49  MUC search           : 0.00
% 3.31/1.49  Cooper               : 0.00
% 3.31/1.49  Total                : 0.76
% 3.31/1.49  Index Insertion      : 0.00
% 3.31/1.49  Index Deletion       : 0.00
% 3.31/1.49  Index Matching       : 0.00
% 3.31/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
