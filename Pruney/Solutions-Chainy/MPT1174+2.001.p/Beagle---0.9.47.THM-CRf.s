%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:52 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 549 expanded)
%              Number of leaves         :   36 ( 233 expanded)
%              Depth                    :   32
%              Number of atoms          :  658 (3133 expanded)
%              Number of equality atoms :   92 ( 505 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_175,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_38,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_844,plain,(
    ! [C_262,A_263,B_264] :
      ( m1_subset_1(C_262,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m2_orders_2(C_262,A_263,B_264)
      | ~ m1_orders_1(B_264,k1_orders_1(u1_struct_0(A_263)))
      | ~ l1_orders_2(A_263)
      | ~ v5_orders_2(A_263)
      | ~ v4_orders_2(A_263)
      | ~ v3_orders_2(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_846,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_844])).

tff(c_849,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_38,c_846])).

tff(c_850,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_849])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k3_orders_2(A_11,B_12,C_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_876,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( r2_orders_2(A_279,B_280,C_281)
      | ~ r2_hidden(B_280,k3_orders_2(A_279,D_282,C_281))
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | ~ v5_orders_2(A_279)
      | ~ v4_orders_2(A_279)
      | ~ v3_orders_2(A_279)
      | v2_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1011,plain,(
    ! [A_330,A_331,D_332,C_333] :
      ( r2_orders_2(A_330,'#skF_1'(A_331,k3_orders_2(A_330,D_332,C_333)),C_333)
      | ~ m1_subset_1(D_332,k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ m1_subset_1(C_333,u1_struct_0(A_330))
      | ~ m1_subset_1('#skF_1'(A_331,k3_orders_2(A_330,D_332,C_333)),u1_struct_0(A_330))
      | ~ l1_orders_2(A_330)
      | ~ v5_orders_2(A_330)
      | ~ v4_orders_2(A_330)
      | ~ v3_orders_2(A_330)
      | v2_struct_0(A_330)
      | k3_orders_2(A_330,D_332,C_333) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_330,D_332,C_333),k1_zfmisc_1(A_331)) ) ),
    inference(resolution,[status(thm)],[c_2,c_876])).

tff(c_1016,plain,(
    ! [A_334,D_335,C_336] :
      ( r2_orders_2(A_334,'#skF_1'(u1_struct_0(A_334),k3_orders_2(A_334,D_335,C_336)),C_336)
      | ~ m1_subset_1(D_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ m1_subset_1(C_336,u1_struct_0(A_334))
      | ~ l1_orders_2(A_334)
      | ~ v5_orders_2(A_334)
      | ~ v4_orders_2(A_334)
      | ~ v3_orders_2(A_334)
      | v2_struct_0(A_334)
      | k3_orders_2(A_334,D_335,C_336) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_334,D_335,C_336),k1_zfmisc_1(u1_struct_0(A_334))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1011])).

tff(c_10,plain,(
    ! [A_4,B_8,C_10] :
      ( r1_orders_2(A_4,B_8,C_10)
      | ~ r2_orders_2(A_4,B_8,C_10)
      | ~ m1_subset_1(C_10,u1_struct_0(A_4))
      | ~ m1_subset_1(B_8,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1020,plain,(
    ! [A_337,D_338,C_339] :
      ( r1_orders_2(A_337,'#skF_1'(u1_struct_0(A_337),k3_orders_2(A_337,D_338,C_339)),C_339)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_337),k3_orders_2(A_337,D_338,C_339)),u1_struct_0(A_337))
      | ~ m1_subset_1(D_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_subset_1(C_339,u1_struct_0(A_337))
      | ~ l1_orders_2(A_337)
      | ~ v5_orders_2(A_337)
      | ~ v4_orders_2(A_337)
      | ~ v3_orders_2(A_337)
      | v2_struct_0(A_337)
      | k3_orders_2(A_337,D_338,C_339) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_337,D_338,C_339),k1_zfmisc_1(u1_struct_0(A_337))) ) ),
    inference(resolution,[status(thm)],[c_1016,c_10])).

tff(c_1025,plain,(
    ! [A_340,D_341,C_342] :
      ( r1_orders_2(A_340,'#skF_1'(u1_struct_0(A_340),k3_orders_2(A_340,D_341,C_342)),C_342)
      | ~ m1_subset_1(D_341,k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ l1_orders_2(A_340)
      | ~ v5_orders_2(A_340)
      | ~ v4_orders_2(A_340)
      | ~ v3_orders_2(A_340)
      | v2_struct_0(A_340)
      | k3_orders_2(A_340,D_341,C_342) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_340,D_341,C_342),k1_zfmisc_1(u1_struct_0(A_340))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1020])).

tff(c_34,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_895,plain,(
    ! [A_287,D_288,B_289,E_290] :
      ( r3_orders_2(A_287,k1_funct_1(D_288,u1_struct_0(A_287)),B_289)
      | ~ r2_hidden(B_289,E_290)
      | ~ m2_orders_2(E_290,A_287,D_288)
      | ~ m1_orders_1(D_288,k1_orders_1(u1_struct_0(A_287)))
      | ~ m1_subset_1(k1_funct_1(D_288,u1_struct_0(A_287)),u1_struct_0(A_287))
      | ~ m1_subset_1(B_289,u1_struct_0(A_287))
      | ~ l1_orders_2(A_287)
      | ~ v5_orders_2(A_287)
      | ~ v4_orders_2(A_287)
      | ~ v3_orders_2(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_936,plain,(
    ! [A_306,D_307,A_308,B_309] :
      ( r3_orders_2(A_306,k1_funct_1(D_307,u1_struct_0(A_306)),'#skF_1'(A_308,B_309))
      | ~ m2_orders_2(B_309,A_306,D_307)
      | ~ m1_orders_1(D_307,k1_orders_1(u1_struct_0(A_306)))
      | ~ m1_subset_1(k1_funct_1(D_307,u1_struct_0(A_306)),u1_struct_0(A_306))
      | ~ m1_subset_1('#skF_1'(A_308,B_309),u1_struct_0(A_306))
      | ~ l1_orders_2(A_306)
      | ~ v5_orders_2(A_306)
      | ~ v4_orders_2(A_306)
      | ~ v3_orders_2(A_306)
      | v2_struct_0(A_306)
      | k1_xboole_0 = B_309
      | ~ m1_subset_1(B_309,k1_zfmisc_1(A_308)) ) ),
    inference(resolution,[status(thm)],[c_2,c_895])).

tff(c_941,plain,(
    ! [A_308,B_309] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_308,B_309))
      | ~ m2_orders_2(B_309,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_308,B_309),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_309
      | ~ m1_subset_1(B_309,k1_zfmisc_1(A_308)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_936])).

tff(c_944,plain,(
    ! [A_308,B_309] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_308,B_309))
      | ~ m2_orders_2(B_309,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_308,B_309),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_309
      | ~ m1_subset_1(B_309,k1_zfmisc_1(A_308)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_34,c_38,c_941])).

tff(c_946,plain,(
    ! [A_310,B_311] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_310,B_311))
      | ~ m2_orders_2(B_311,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_310,B_311),u1_struct_0('#skF_2'))
      | k1_xboole_0 = B_311
      | ~ m1_subset_1(B_311,k1_zfmisc_1(A_310)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_944])).

tff(c_952,plain,(
    ! [B_312] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_312))
      | ~ m2_orders_2(B_312,'#skF_2','#skF_4')
      | k1_xboole_0 = B_312
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_946])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_orders_2(A_18,B_19,C_20)
      | ~ r3_orders_2(A_18,B_19,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_18))
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_954,plain,(
    ! [B_312] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_312))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_312),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_312,'#skF_2','#skF_4')
      | k1_xboole_0 = B_312
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_952,c_20])).

tff(c_957,plain,(
    ! [B_312] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_312))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_312),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_312,'#skF_2','#skF_4')
      | k1_xboole_0 = B_312
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_954])).

tff(c_959,plain,(
    ! [B_313] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_313))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_313),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_313,'#skF_2','#skF_4')
      | k1_xboole_0 = B_313
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_957])).

tff(c_965,plain,(
    ! [B_314] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_314))
      | ~ m2_orders_2(B_314,'#skF_2','#skF_4')
      | k1_xboole_0 = B_314
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_959])).

tff(c_22,plain,(
    ! [C_27,B_25,A_21] :
      ( C_27 = B_25
      | ~ r1_orders_2(A_21,C_27,B_25)
      | ~ r1_orders_2(A_21,B_25,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ m1_subset_1(B_25,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21)
      | ~ v5_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_967,plain,(
    ! [B_314] :
      ( '#skF_1'(u1_struct_0('#skF_2'),B_314) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_314),'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_314),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ m2_orders_2(B_314,'#skF_2','#skF_4')
      | k1_xboole_0 = B_314
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_965,c_22])).

tff(c_976,plain,(
    ! [B_319] :
      ( '#skF_1'(u1_struct_0('#skF_2'),B_319) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_319),'#skF_3')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_319),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_319,'#skF_2','#skF_4')
      | k1_xboole_0 = B_319
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_967])).

tff(c_981,plain,(
    ! [B_2] :
      ( '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | ~ m2_orders_2(B_2,'#skF_2','#skF_4')
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_976])).

tff(c_1029,plain,(
    ! [D_341] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_341,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',D_341,'#skF_3'),'#skF_2','#skF_4')
      | ~ m1_subset_1(D_341,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_341,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_341,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1025,c_981])).

tff(c_1034,plain,(
    ! [D_341] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_341,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',D_341,'#skF_3'),'#skF_2','#skF_4')
      | ~ m1_subset_1(D_341,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_341,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_341,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1029])).

tff(c_1038,plain,(
    ! [D_350] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_350,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',D_350,'#skF_3'),'#skF_2','#skF_4')
      | ~ m1_subset_1(D_350,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_350,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_350,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1034])).

tff(c_1042,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',B_12,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1038])).

tff(c_1045,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',B_12,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1042])).

tff(c_1047,plain,(
    ! [B_351] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_351,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',B_351,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_351,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1045])).

tff(c_1051,plain,(
    ! [B_12,C_13] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1047])).

tff(c_1061,plain,(
    ! [B_12,C_13] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1051])).

tff(c_1068,plain,(
    ! [B_352,C_353] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1061])).

tff(c_1015,plain,(
    ! [A_330,D_332,C_333] :
      ( r2_orders_2(A_330,'#skF_1'(u1_struct_0(A_330),k3_orders_2(A_330,D_332,C_333)),C_333)
      | ~ m1_subset_1(D_332,k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ m1_subset_1(C_333,u1_struct_0(A_330))
      | ~ l1_orders_2(A_330)
      | ~ v5_orders_2(A_330)
      | ~ v4_orders_2(A_330)
      | ~ v3_orders_2(A_330)
      | v2_struct_0(A_330)
      | k3_orders_2(A_330,D_332,C_333) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_330,D_332,C_333),k1_zfmisc_1(u1_struct_0(A_330))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1011])).

tff(c_1077,plain,(
    ! [B_352,C_353] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_352,C_353),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_1015])).

tff(c_1132,plain,(
    ! [B_352,C_353] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_352,C_353),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1077])).

tff(c_1133,plain,(
    ! [B_352,C_353] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_352,C_353),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_352,C_353),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1132])).

tff(c_1251,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1133])).

tff(c_8,plain,(
    ! [A_4,C_10] :
      ( ~ r2_orders_2(A_4,C_10,C_10)
      | ~ m1_subset_1(C_10,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1255,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1251,c_8])).

tff(c_1262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1255])).

tff(c_1264,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1133])).

tff(c_1024,plain,(
    ! [A_337,D_338,C_339] :
      ( r1_orders_2(A_337,'#skF_1'(u1_struct_0(A_337),k3_orders_2(A_337,D_338,C_339)),C_339)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_subset_1(C_339,u1_struct_0(A_337))
      | ~ l1_orders_2(A_337)
      | ~ v5_orders_2(A_337)
      | ~ v4_orders_2(A_337)
      | ~ v3_orders_2(A_337)
      | v2_struct_0(A_337)
      | k3_orders_2(A_337,D_338,C_339) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_337,D_338,C_339),k1_zfmisc_1(u1_struct_0(A_337))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1020])).

tff(c_862,plain,(
    ! [B_272,D_273,A_274,C_275] :
      ( r2_hidden(B_272,D_273)
      | ~ r2_hidden(B_272,k3_orders_2(A_274,D_273,C_275))
      | ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ m1_subset_1(C_275,u1_struct_0(A_274))
      | ~ m1_subset_1(B_272,u1_struct_0(A_274))
      | ~ l1_orders_2(A_274)
      | ~ v5_orders_2(A_274)
      | ~ v4_orders_2(A_274)
      | ~ v3_orders_2(A_274)
      | v2_struct_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_971,plain,(
    ! [A_315,A_316,D_317,C_318] :
      ( r2_hidden('#skF_1'(A_315,k3_orders_2(A_316,D_317,C_318)),D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ m1_subset_1(C_318,u1_struct_0(A_316))
      | ~ m1_subset_1('#skF_1'(A_315,k3_orders_2(A_316,D_317,C_318)),u1_struct_0(A_316))
      | ~ l1_orders_2(A_316)
      | ~ v5_orders_2(A_316)
      | ~ v4_orders_2(A_316)
      | ~ v3_orders_2(A_316)
      | v2_struct_0(A_316)
      | k3_orders_2(A_316,D_317,C_318) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_316,D_317,C_318),k1_zfmisc_1(A_315)) ) ),
    inference(resolution,[status(thm)],[c_2,c_862])).

tff(c_983,plain,(
    ! [A_321,D_322,C_323] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_321),k3_orders_2(A_321,D_322,C_323)),D_322)
      | ~ m1_subset_1(D_322,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ m1_subset_1(C_323,u1_struct_0(A_321))
      | ~ l1_orders_2(A_321)
      | ~ v5_orders_2(A_321)
      | ~ v4_orders_2(A_321)
      | ~ v3_orders_2(A_321)
      | v2_struct_0(A_321)
      | k3_orders_2(A_321,D_322,C_323) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_321,D_322,C_323),k1_zfmisc_1(u1_struct_0(A_321))) ) ),
    inference(resolution,[status(thm)],[c_4,c_971])).

tff(c_30,plain,(
    ! [A_43,D_71,B_59,E_73] :
      ( r3_orders_2(A_43,k1_funct_1(D_71,u1_struct_0(A_43)),B_59)
      | ~ r2_hidden(B_59,E_73)
      | ~ m2_orders_2(E_73,A_43,D_71)
      | ~ m1_orders_1(D_71,k1_orders_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(k1_funct_1(D_71,u1_struct_0(A_43)),u1_struct_0(A_43))
      | ~ m1_subset_1(B_59,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | ~ v3_orders_2(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1318,plain,(
    ! [A_380,D_377,C_376,A_379,D_378] :
      ( r3_orders_2(A_379,k1_funct_1(D_377,u1_struct_0(A_379)),'#skF_1'(u1_struct_0(A_380),k3_orders_2(A_380,D_378,C_376)))
      | ~ m2_orders_2(D_378,A_379,D_377)
      | ~ m1_orders_1(D_377,k1_orders_1(u1_struct_0(A_379)))
      | ~ m1_subset_1(k1_funct_1(D_377,u1_struct_0(A_379)),u1_struct_0(A_379))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_380),k3_orders_2(A_380,D_378,C_376)),u1_struct_0(A_379))
      | ~ l1_orders_2(A_379)
      | ~ v5_orders_2(A_379)
      | ~ v4_orders_2(A_379)
      | ~ v3_orders_2(A_379)
      | v2_struct_0(A_379)
      | ~ m1_subset_1(D_378,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ m1_subset_1(C_376,u1_struct_0(A_380))
      | ~ l1_orders_2(A_380)
      | ~ v5_orders_2(A_380)
      | ~ v4_orders_2(A_380)
      | ~ v3_orders_2(A_380)
      | v2_struct_0(A_380)
      | k3_orders_2(A_380,D_378,C_376) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_380,D_378,C_376),k1_zfmisc_1(u1_struct_0(A_380))) ) ),
    inference(resolution,[status(thm)],[c_983,c_30])).

tff(c_1323,plain,(
    ! [A_380,D_378,C_376] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_380),k3_orders_2(A_380,D_378,C_376)))
      | ~ m2_orders_2(D_378,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_380),k3_orders_2(A_380,D_378,C_376)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_378,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ m1_subset_1(C_376,u1_struct_0(A_380))
      | ~ l1_orders_2(A_380)
      | ~ v5_orders_2(A_380)
      | ~ v4_orders_2(A_380)
      | ~ v3_orders_2(A_380)
      | v2_struct_0(A_380)
      | k3_orders_2(A_380,D_378,C_376) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_380,D_378,C_376),k1_zfmisc_1(u1_struct_0(A_380))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1318])).

tff(c_1326,plain,(
    ! [A_380,D_378,C_376] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_380),k3_orders_2(A_380,D_378,C_376)))
      | ~ m2_orders_2(D_378,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_380),k3_orders_2(A_380,D_378,C_376)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_378,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ m1_subset_1(C_376,u1_struct_0(A_380))
      | ~ l1_orders_2(A_380)
      | ~ v5_orders_2(A_380)
      | ~ v4_orders_2(A_380)
      | ~ v3_orders_2(A_380)
      | v2_struct_0(A_380)
      | k3_orders_2(A_380,D_378,C_376) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_380,D_378,C_376),k1_zfmisc_1(u1_struct_0(A_380))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_34,c_38,c_1323])).

tff(c_1328,plain,(
    ! [A_381,D_382,C_383] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_381),k3_orders_2(A_381,D_382,C_383)))
      | ~ m2_orders_2(D_382,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_381),k3_orders_2(A_381,D_382,C_383)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ m1_subset_1(C_383,u1_struct_0(A_381))
      | ~ l1_orders_2(A_381)
      | ~ v5_orders_2(A_381)
      | ~ v4_orders_2(A_381)
      | ~ v3_orders_2(A_381)
      | v2_struct_0(A_381)
      | k3_orders_2(A_381,D_382,C_383) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_381,D_382,C_383),k1_zfmisc_1(u1_struct_0(A_381))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1326])).

tff(c_1332,plain,(
    ! [D_382,C_383] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_382,C_383)))
      | ~ m2_orders_2(D_382,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_383,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_382,C_383) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_382,C_383),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1328])).

tff(c_1335,plain,(
    ! [D_382,C_383] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_382,C_383)))
      | ~ m2_orders_2(D_382,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_383,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_382,C_383) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_382,C_383),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1332])).

tff(c_1337,plain,(
    ! [D_384,C_385] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_384,C_385)))
      | ~ m2_orders_2(D_384,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_384,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_385,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_384,C_385) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_384,C_385),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1335])).

tff(c_1339,plain,(
    ! [D_384,C_385] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_384,C_385)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_384,C_385)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_384,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_384,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_385,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_384,C_385) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_384,C_385),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1337,c_20])).

tff(c_1342,plain,(
    ! [D_384,C_385] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_384,C_385)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_384,C_385)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_384,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_384,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_385,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_384,C_385) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_384,C_385),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_1339])).

tff(c_1344,plain,(
    ! [D_386,C_387] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_386,C_387)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_386,C_387)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(D_386,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_386,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_387,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_386,C_387) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_386,C_387),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1342])).

tff(c_1349,plain,(
    ! [D_388,C_389] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_388,C_389)))
      | ~ m2_orders_2(D_388,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_388,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_389,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_388,C_389) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_388,C_389),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1344])).

tff(c_1351,plain,(
    ! [D_388,C_389] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_388,C_389)) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_388,C_389)),'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_388,C_389)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ m2_orders_2(D_388,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_388,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_389,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_388,C_389) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_388,C_389),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1349,c_22])).

tff(c_1355,plain,(
    ! [D_390,C_391] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(D_390,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_390,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_391,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_390,C_391) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_390,C_391),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1351])).

tff(c_1360,plain,(
    ! [D_392,C_393] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_392,C_393)) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_392,C_393)),'#skF_3')
      | ~ m2_orders_2(D_392,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_392,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_393,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_392,C_393) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_392,C_393),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1355])).

tff(c_1364,plain,(
    ! [D_338] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_338,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(D_338,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_338,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_338,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_338,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1024,c_1360])).

tff(c_1367,plain,(
    ! [D_338] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_338,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(D_338,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_338,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_338,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_338,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1364])).

tff(c_1369,plain,(
    ! [D_394] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_394,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(D_394,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_394,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_394,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_394,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1367])).

tff(c_1373,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_12,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1369])).

tff(c_1376,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_12,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1373])).

tff(c_1378,plain,(
    ! [B_395] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_395,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_395,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_395,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_395,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1376])).

tff(c_1385,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_850,c_1378])).

tff(c_1396,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1385])).

tff(c_1397,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1396])).

tff(c_1431,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1397,c_1015])).

tff(c_1504,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_850,c_1431])).

tff(c_1505,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_50,c_1264,c_1504])).

tff(c_1550,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1505])).

tff(c_1553,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_850,c_40,c_1550])).

tff(c_1555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:20:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.73/1.82  
% 4.73/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.82  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.77/1.82  
% 4.77/1.82  %Foreground sorts:
% 4.77/1.82  
% 4.77/1.82  
% 4.77/1.82  %Background operators:
% 4.77/1.82  
% 4.77/1.82  
% 4.77/1.82  %Foreground operators:
% 4.77/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.77/1.82  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.77/1.82  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.82  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.77/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.82  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 4.77/1.82  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 4.77/1.82  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 4.77/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.82  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.77/1.82  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.77/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.77/1.82  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.77/1.82  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.82  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.77/1.82  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.77/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.77/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.77/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.82  
% 4.77/1.85  tff(f_200, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_orders_2)).
% 4.77/1.85  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 4.77/1.85  tff(f_69, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 4.77/1.85  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.77/1.85  tff(f_146, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 4.77/1.85  tff(f_52, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 4.77/1.85  tff(f_175, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_orders_2)).
% 4.77/1.85  tff(f_104, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.77/1.85  tff(f_120, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 4.77/1.85  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_38, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_844, plain, (![C_262, A_263, B_264]: (m1_subset_1(C_262, k1_zfmisc_1(u1_struct_0(A_263))) | ~m2_orders_2(C_262, A_263, B_264) | ~m1_orders_1(B_264, k1_orders_1(u1_struct_0(A_263))) | ~l1_orders_2(A_263) | ~v5_orders_2(A_263) | ~v4_orders_2(A_263) | ~v3_orders_2(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.77/1.85  tff(c_846, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_844])).
% 4.77/1.85  tff(c_849, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_38, c_846])).
% 4.77/1.85  tff(c_850, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_849])).
% 4.77/1.85  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_12, plain, (![A_11, B_12, C_13]: (m1_subset_1(k3_orders_2(A_11, B_12, C_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.77/1.85  tff(c_32, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.85  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.85  tff(c_876, plain, (![A_279, B_280, C_281, D_282]: (r2_orders_2(A_279, B_280, C_281) | ~r2_hidden(B_280, k3_orders_2(A_279, D_282, C_281)) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0(A_279))) | ~m1_subset_1(C_281, u1_struct_0(A_279)) | ~m1_subset_1(B_280, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | ~v5_orders_2(A_279) | ~v4_orders_2(A_279) | ~v3_orders_2(A_279) | v2_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.77/1.85  tff(c_1011, plain, (![A_330, A_331, D_332, C_333]: (r2_orders_2(A_330, '#skF_1'(A_331, k3_orders_2(A_330, D_332, C_333)), C_333) | ~m1_subset_1(D_332, k1_zfmisc_1(u1_struct_0(A_330))) | ~m1_subset_1(C_333, u1_struct_0(A_330)) | ~m1_subset_1('#skF_1'(A_331, k3_orders_2(A_330, D_332, C_333)), u1_struct_0(A_330)) | ~l1_orders_2(A_330) | ~v5_orders_2(A_330) | ~v4_orders_2(A_330) | ~v3_orders_2(A_330) | v2_struct_0(A_330) | k3_orders_2(A_330, D_332, C_333)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_330, D_332, C_333), k1_zfmisc_1(A_331)))), inference(resolution, [status(thm)], [c_2, c_876])).
% 4.77/1.85  tff(c_1016, plain, (![A_334, D_335, C_336]: (r2_orders_2(A_334, '#skF_1'(u1_struct_0(A_334), k3_orders_2(A_334, D_335, C_336)), C_336) | ~m1_subset_1(D_335, k1_zfmisc_1(u1_struct_0(A_334))) | ~m1_subset_1(C_336, u1_struct_0(A_334)) | ~l1_orders_2(A_334) | ~v5_orders_2(A_334) | ~v4_orders_2(A_334) | ~v3_orders_2(A_334) | v2_struct_0(A_334) | k3_orders_2(A_334, D_335, C_336)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_334, D_335, C_336), k1_zfmisc_1(u1_struct_0(A_334))))), inference(resolution, [status(thm)], [c_4, c_1011])).
% 4.77/1.85  tff(c_10, plain, (![A_4, B_8, C_10]: (r1_orders_2(A_4, B_8, C_10) | ~r2_orders_2(A_4, B_8, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_4)) | ~m1_subset_1(B_8, u1_struct_0(A_4)) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.77/1.85  tff(c_1020, plain, (![A_337, D_338, C_339]: (r1_orders_2(A_337, '#skF_1'(u1_struct_0(A_337), k3_orders_2(A_337, D_338, C_339)), C_339) | ~m1_subset_1('#skF_1'(u1_struct_0(A_337), k3_orders_2(A_337, D_338, C_339)), u1_struct_0(A_337)) | ~m1_subset_1(D_338, k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_subset_1(C_339, u1_struct_0(A_337)) | ~l1_orders_2(A_337) | ~v5_orders_2(A_337) | ~v4_orders_2(A_337) | ~v3_orders_2(A_337) | v2_struct_0(A_337) | k3_orders_2(A_337, D_338, C_339)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_337, D_338, C_339), k1_zfmisc_1(u1_struct_0(A_337))))), inference(resolution, [status(thm)], [c_1016, c_10])).
% 4.77/1.85  tff(c_1025, plain, (![A_340, D_341, C_342]: (r1_orders_2(A_340, '#skF_1'(u1_struct_0(A_340), k3_orders_2(A_340, D_341, C_342)), C_342) | ~m1_subset_1(D_341, k1_zfmisc_1(u1_struct_0(A_340))) | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~l1_orders_2(A_340) | ~v5_orders_2(A_340) | ~v4_orders_2(A_340) | ~v3_orders_2(A_340) | v2_struct_0(A_340) | k3_orders_2(A_340, D_341, C_342)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_340, D_341, C_342), k1_zfmisc_1(u1_struct_0(A_340))))), inference(resolution, [status(thm)], [c_4, c_1020])).
% 4.77/1.85  tff(c_34, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.77/1.85  tff(c_895, plain, (![A_287, D_288, B_289, E_290]: (r3_orders_2(A_287, k1_funct_1(D_288, u1_struct_0(A_287)), B_289) | ~r2_hidden(B_289, E_290) | ~m2_orders_2(E_290, A_287, D_288) | ~m1_orders_1(D_288, k1_orders_1(u1_struct_0(A_287))) | ~m1_subset_1(k1_funct_1(D_288, u1_struct_0(A_287)), u1_struct_0(A_287)) | ~m1_subset_1(B_289, u1_struct_0(A_287)) | ~l1_orders_2(A_287) | ~v5_orders_2(A_287) | ~v4_orders_2(A_287) | ~v3_orders_2(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.77/1.85  tff(c_936, plain, (![A_306, D_307, A_308, B_309]: (r3_orders_2(A_306, k1_funct_1(D_307, u1_struct_0(A_306)), '#skF_1'(A_308, B_309)) | ~m2_orders_2(B_309, A_306, D_307) | ~m1_orders_1(D_307, k1_orders_1(u1_struct_0(A_306))) | ~m1_subset_1(k1_funct_1(D_307, u1_struct_0(A_306)), u1_struct_0(A_306)) | ~m1_subset_1('#skF_1'(A_308, B_309), u1_struct_0(A_306)) | ~l1_orders_2(A_306) | ~v5_orders_2(A_306) | ~v4_orders_2(A_306) | ~v3_orders_2(A_306) | v2_struct_0(A_306) | k1_xboole_0=B_309 | ~m1_subset_1(B_309, k1_zfmisc_1(A_308)))), inference(resolution, [status(thm)], [c_2, c_895])).
% 4.77/1.85  tff(c_941, plain, (![A_308, B_309]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_308, B_309)) | ~m2_orders_2(B_309, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_308, B_309), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=B_309 | ~m1_subset_1(B_309, k1_zfmisc_1(A_308)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_936])).
% 4.77/1.85  tff(c_944, plain, (![A_308, B_309]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_308, B_309)) | ~m2_orders_2(B_309, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_308, B_309), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=B_309 | ~m1_subset_1(B_309, k1_zfmisc_1(A_308)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_34, c_38, c_941])).
% 4.77/1.85  tff(c_946, plain, (![A_310, B_311]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_310, B_311)) | ~m2_orders_2(B_311, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_310, B_311), u1_struct_0('#skF_2')) | k1_xboole_0=B_311 | ~m1_subset_1(B_311, k1_zfmisc_1(A_310)))), inference(negUnitSimplification, [status(thm)], [c_50, c_944])).
% 4.77/1.85  tff(c_952, plain, (![B_312]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_312)) | ~m2_orders_2(B_312, '#skF_2', '#skF_4') | k1_xboole_0=B_312 | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_946])).
% 4.77/1.85  tff(c_20, plain, (![A_18, B_19, C_20]: (r1_orders_2(A_18, B_19, C_20) | ~r3_orders_2(A_18, B_19, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_18)) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.77/1.85  tff(c_954, plain, (![B_312]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_312)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_312), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_312, '#skF_2', '#skF_4') | k1_xboole_0=B_312 | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_952, c_20])).
% 4.77/1.85  tff(c_957, plain, (![B_312]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_312)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_312), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_312, '#skF_2', '#skF_4') | k1_xboole_0=B_312 | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_954])).
% 4.77/1.85  tff(c_959, plain, (![B_313]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_313)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_313), u1_struct_0('#skF_2')) | ~m2_orders_2(B_313, '#skF_2', '#skF_4') | k1_xboole_0=B_313 | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_957])).
% 4.77/1.85  tff(c_965, plain, (![B_314]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_314)) | ~m2_orders_2(B_314, '#skF_2', '#skF_4') | k1_xboole_0=B_314 | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_959])).
% 4.77/1.85  tff(c_22, plain, (![C_27, B_25, A_21]: (C_27=B_25 | ~r1_orders_2(A_21, C_27, B_25) | ~r1_orders_2(A_21, B_25, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~m1_subset_1(B_25, u1_struct_0(A_21)) | ~l1_orders_2(A_21) | ~v5_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.77/1.85  tff(c_967, plain, (![B_314]: ('#skF_1'(u1_struct_0('#skF_2'), B_314)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_314), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_314), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~m2_orders_2(B_314, '#skF_2', '#skF_4') | k1_xboole_0=B_314 | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_965, c_22])).
% 4.77/1.85  tff(c_976, plain, (![B_319]: ('#skF_1'(u1_struct_0('#skF_2'), B_319)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_319), '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_319), u1_struct_0('#skF_2')) | ~m2_orders_2(B_319, '#skF_2', '#skF_4') | k1_xboole_0=B_319 | ~m1_subset_1(B_319, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_967])).
% 4.77/1.85  tff(c_981, plain, (![B_2]: ('#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | ~m2_orders_2(B_2, '#skF_2', '#skF_4') | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_976])).
% 4.77/1.85  tff(c_1029, plain, (![D_341]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_341, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', D_341, '#skF_3'), '#skF_2', '#skF_4') | ~m1_subset_1(D_341, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_341, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_341, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1025, c_981])).
% 4.77/1.85  tff(c_1034, plain, (![D_341]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_341, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', D_341, '#skF_3'), '#skF_2', '#skF_4') | ~m1_subset_1(D_341, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_341, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_341, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1029])).
% 4.77/1.85  tff(c_1038, plain, (![D_350]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_350, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', D_350, '#skF_3'), '#skF_2', '#skF_4') | ~m1_subset_1(D_350, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_350, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_350, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1034])).
% 4.77/1.85  tff(c_1042, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', B_12, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1038])).
% 4.77/1.85  tff(c_1045, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', B_12, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1042])).
% 4.77/1.85  tff(c_1047, plain, (![B_351]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_351, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', B_351, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_351, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1045])).
% 4.77/1.85  tff(c_1051, plain, (![B_12, C_13]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_13, u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1047])).
% 4.77/1.85  tff(c_1061, plain, (![B_12, C_13]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_13, u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1051])).
% 4.77/1.85  tff(c_1068, plain, (![B_352, C_353]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_353, u1_struct_0('#skF_2')) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1061])).
% 4.77/1.85  tff(c_1015, plain, (![A_330, D_332, C_333]: (r2_orders_2(A_330, '#skF_1'(u1_struct_0(A_330), k3_orders_2(A_330, D_332, C_333)), C_333) | ~m1_subset_1(D_332, k1_zfmisc_1(u1_struct_0(A_330))) | ~m1_subset_1(C_333, u1_struct_0(A_330)) | ~l1_orders_2(A_330) | ~v5_orders_2(A_330) | ~v4_orders_2(A_330) | ~v3_orders_2(A_330) | v2_struct_0(A_330) | k3_orders_2(A_330, D_332, C_333)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_330, D_332, C_333), k1_zfmisc_1(u1_struct_0(A_330))))), inference(resolution, [status(thm)], [c_4, c_1011])).
% 4.77/1.85  tff(c_1077, plain, (![B_352, C_353]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', B_352, C_353), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_353, u1_struct_0('#skF_2')) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_1015])).
% 4.77/1.85  tff(c_1132, plain, (![B_352, C_353]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', B_352, C_353), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_353, u1_struct_0('#skF_2')) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1077])).
% 4.77/1.85  tff(c_1133, plain, (![B_352, C_353]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', B_352, C_353), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_352, C_353), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_353, u1_struct_0('#skF_2')) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1132])).
% 4.77/1.85  tff(c_1251, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1133])).
% 4.77/1.85  tff(c_8, plain, (![A_4, C_10]: (~r2_orders_2(A_4, C_10, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_4)) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.77/1.85  tff(c_1255, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1251, c_8])).
% 4.77/1.85  tff(c_1262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1255])).
% 4.77/1.85  tff(c_1264, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1133])).
% 4.77/1.85  tff(c_1024, plain, (![A_337, D_338, C_339]: (r1_orders_2(A_337, '#skF_1'(u1_struct_0(A_337), k3_orders_2(A_337, D_338, C_339)), C_339) | ~m1_subset_1(D_338, k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_subset_1(C_339, u1_struct_0(A_337)) | ~l1_orders_2(A_337) | ~v5_orders_2(A_337) | ~v4_orders_2(A_337) | ~v3_orders_2(A_337) | v2_struct_0(A_337) | k3_orders_2(A_337, D_338, C_339)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_337, D_338, C_339), k1_zfmisc_1(u1_struct_0(A_337))))), inference(resolution, [status(thm)], [c_4, c_1020])).
% 4.77/1.85  tff(c_862, plain, (![B_272, D_273, A_274, C_275]: (r2_hidden(B_272, D_273) | ~r2_hidden(B_272, k3_orders_2(A_274, D_273, C_275)) | ~m1_subset_1(D_273, k1_zfmisc_1(u1_struct_0(A_274))) | ~m1_subset_1(C_275, u1_struct_0(A_274)) | ~m1_subset_1(B_272, u1_struct_0(A_274)) | ~l1_orders_2(A_274) | ~v5_orders_2(A_274) | ~v4_orders_2(A_274) | ~v3_orders_2(A_274) | v2_struct_0(A_274))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.77/1.85  tff(c_971, plain, (![A_315, A_316, D_317, C_318]: (r2_hidden('#skF_1'(A_315, k3_orders_2(A_316, D_317, C_318)), D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~m1_subset_1(C_318, u1_struct_0(A_316)) | ~m1_subset_1('#skF_1'(A_315, k3_orders_2(A_316, D_317, C_318)), u1_struct_0(A_316)) | ~l1_orders_2(A_316) | ~v5_orders_2(A_316) | ~v4_orders_2(A_316) | ~v3_orders_2(A_316) | v2_struct_0(A_316) | k3_orders_2(A_316, D_317, C_318)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_316, D_317, C_318), k1_zfmisc_1(A_315)))), inference(resolution, [status(thm)], [c_2, c_862])).
% 4.77/1.85  tff(c_983, plain, (![A_321, D_322, C_323]: (r2_hidden('#skF_1'(u1_struct_0(A_321), k3_orders_2(A_321, D_322, C_323)), D_322) | ~m1_subset_1(D_322, k1_zfmisc_1(u1_struct_0(A_321))) | ~m1_subset_1(C_323, u1_struct_0(A_321)) | ~l1_orders_2(A_321) | ~v5_orders_2(A_321) | ~v4_orders_2(A_321) | ~v3_orders_2(A_321) | v2_struct_0(A_321) | k3_orders_2(A_321, D_322, C_323)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_321, D_322, C_323), k1_zfmisc_1(u1_struct_0(A_321))))), inference(resolution, [status(thm)], [c_4, c_971])).
% 4.77/1.85  tff(c_30, plain, (![A_43, D_71, B_59, E_73]: (r3_orders_2(A_43, k1_funct_1(D_71, u1_struct_0(A_43)), B_59) | ~r2_hidden(B_59, E_73) | ~m2_orders_2(E_73, A_43, D_71) | ~m1_orders_1(D_71, k1_orders_1(u1_struct_0(A_43))) | ~m1_subset_1(k1_funct_1(D_71, u1_struct_0(A_43)), u1_struct_0(A_43)) | ~m1_subset_1(B_59, u1_struct_0(A_43)) | ~l1_orders_2(A_43) | ~v5_orders_2(A_43) | ~v4_orders_2(A_43) | ~v3_orders_2(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.77/1.85  tff(c_1318, plain, (![A_380, D_377, C_376, A_379, D_378]: (r3_orders_2(A_379, k1_funct_1(D_377, u1_struct_0(A_379)), '#skF_1'(u1_struct_0(A_380), k3_orders_2(A_380, D_378, C_376))) | ~m2_orders_2(D_378, A_379, D_377) | ~m1_orders_1(D_377, k1_orders_1(u1_struct_0(A_379))) | ~m1_subset_1(k1_funct_1(D_377, u1_struct_0(A_379)), u1_struct_0(A_379)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_380), k3_orders_2(A_380, D_378, C_376)), u1_struct_0(A_379)) | ~l1_orders_2(A_379) | ~v5_orders_2(A_379) | ~v4_orders_2(A_379) | ~v3_orders_2(A_379) | v2_struct_0(A_379) | ~m1_subset_1(D_378, k1_zfmisc_1(u1_struct_0(A_380))) | ~m1_subset_1(C_376, u1_struct_0(A_380)) | ~l1_orders_2(A_380) | ~v5_orders_2(A_380) | ~v4_orders_2(A_380) | ~v3_orders_2(A_380) | v2_struct_0(A_380) | k3_orders_2(A_380, D_378, C_376)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_380, D_378, C_376), k1_zfmisc_1(u1_struct_0(A_380))))), inference(resolution, [status(thm)], [c_983, c_30])).
% 4.77/1.85  tff(c_1323, plain, (![A_380, D_378, C_376]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_380), k3_orders_2(A_380, D_378, C_376))) | ~m2_orders_2(D_378, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0(A_380), k3_orders_2(A_380, D_378, C_376)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(D_378, k1_zfmisc_1(u1_struct_0(A_380))) | ~m1_subset_1(C_376, u1_struct_0(A_380)) | ~l1_orders_2(A_380) | ~v5_orders_2(A_380) | ~v4_orders_2(A_380) | ~v3_orders_2(A_380) | v2_struct_0(A_380) | k3_orders_2(A_380, D_378, C_376)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_380, D_378, C_376), k1_zfmisc_1(u1_struct_0(A_380))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1318])).
% 4.77/1.85  tff(c_1326, plain, (![A_380, D_378, C_376]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_380), k3_orders_2(A_380, D_378, C_376))) | ~m2_orders_2(D_378, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_380), k3_orders_2(A_380, D_378, C_376)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(D_378, k1_zfmisc_1(u1_struct_0(A_380))) | ~m1_subset_1(C_376, u1_struct_0(A_380)) | ~l1_orders_2(A_380) | ~v5_orders_2(A_380) | ~v4_orders_2(A_380) | ~v3_orders_2(A_380) | v2_struct_0(A_380) | k3_orders_2(A_380, D_378, C_376)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_380, D_378, C_376), k1_zfmisc_1(u1_struct_0(A_380))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_34, c_38, c_1323])).
% 4.77/1.85  tff(c_1328, plain, (![A_381, D_382, C_383]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_381), k3_orders_2(A_381, D_382, C_383))) | ~m2_orders_2(D_382, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_381), k3_orders_2(A_381, D_382, C_383)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~m1_subset_1(C_383, u1_struct_0(A_381)) | ~l1_orders_2(A_381) | ~v5_orders_2(A_381) | ~v4_orders_2(A_381) | ~v3_orders_2(A_381) | v2_struct_0(A_381) | k3_orders_2(A_381, D_382, C_383)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_381, D_382, C_383), k1_zfmisc_1(u1_struct_0(A_381))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1326])).
% 4.77/1.85  tff(c_1332, plain, (![D_382, C_383]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_382, C_383))) | ~m2_orders_2(D_382, '#skF_2', '#skF_4') | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_383, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_382, C_383)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_382, C_383), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1328])).
% 4.77/1.85  tff(c_1335, plain, (![D_382, C_383]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_382, C_383))) | ~m2_orders_2(D_382, '#skF_2', '#skF_4') | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_383, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_382, C_383)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_382, C_383), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1332])).
% 4.77/1.85  tff(c_1337, plain, (![D_384, C_385]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_384, C_385))) | ~m2_orders_2(D_384, '#skF_2', '#skF_4') | ~m1_subset_1(D_384, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_385, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_384, C_385)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_384, C_385), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1335])).
% 4.77/1.85  tff(c_1339, plain, (![D_384, C_385]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_384, C_385))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_384, C_385)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(D_384, '#skF_2', '#skF_4') | ~m1_subset_1(D_384, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_385, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_384, C_385)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_384, C_385), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1337, c_20])).
% 4.77/1.85  tff(c_1342, plain, (![D_384, C_385]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_384, C_385))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_384, C_385)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(D_384, '#skF_2', '#skF_4') | ~m1_subset_1(D_384, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_385, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_384, C_385)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_384, C_385), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_1339])).
% 4.77/1.85  tff(c_1344, plain, (![D_386, C_387]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_386, C_387))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_386, C_387)), u1_struct_0('#skF_2')) | ~m2_orders_2(D_386, '#skF_2', '#skF_4') | ~m1_subset_1(D_386, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_387, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_386, C_387)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_386, C_387), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1342])).
% 4.77/1.85  tff(c_1349, plain, (![D_388, C_389]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_388, C_389))) | ~m2_orders_2(D_388, '#skF_2', '#skF_4') | ~m1_subset_1(D_388, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_389, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_388, C_389)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_388, C_389), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1344])).
% 4.77/1.85  tff(c_1351, plain, (![D_388, C_389]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_388, C_389))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_388, C_389)), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_388, C_389)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~m2_orders_2(D_388, '#skF_2', '#skF_4') | ~m1_subset_1(D_388, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_389, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_388, C_389)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_388, C_389), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1349, c_22])).
% 4.77/1.85  tff(c_1355, plain, (![D_390, C_391]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391)), '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391)), u1_struct_0('#skF_2')) | ~m2_orders_2(D_390, '#skF_2', '#skF_4') | ~m1_subset_1(D_390, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_391, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_390, C_391)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_390, C_391), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1351])).
% 4.77/1.85  tff(c_1360, plain, (![D_392, C_393]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_392, C_393))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_392, C_393)), '#skF_3') | ~m2_orders_2(D_392, '#skF_2', '#skF_4') | ~m1_subset_1(D_392, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_393, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_392, C_393)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_392, C_393), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1355])).
% 4.77/1.85  tff(c_1364, plain, (![D_338]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_338, '#skF_3'))='#skF_3' | ~m2_orders_2(D_338, '#skF_2', '#skF_4') | ~m1_subset_1(D_338, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_338, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_338, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1024, c_1360])).
% 4.77/1.85  tff(c_1367, plain, (![D_338]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_338, '#skF_3'))='#skF_3' | ~m2_orders_2(D_338, '#skF_2', '#skF_4') | ~m1_subset_1(D_338, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_338, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_338, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1364])).
% 4.77/1.85  tff(c_1369, plain, (![D_394]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_394, '#skF_3'))='#skF_3' | ~m2_orders_2(D_394, '#skF_2', '#skF_4') | ~m1_subset_1(D_394, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_394, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_394, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1367])).
% 4.77/1.85  tff(c_1373, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(B_12, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1369])).
% 4.77/1.85  tff(c_1376, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(B_12, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1373])).
% 4.77/1.85  tff(c_1378, plain, (![B_395]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_395, '#skF_3'))='#skF_3' | ~m2_orders_2(B_395, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_395, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_395, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1376])).
% 4.77/1.85  tff(c_1385, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_850, c_1378])).
% 4.77/1.85  tff(c_1396, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1385])).
% 4.77/1.85  tff(c_1397, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_32, c_1396])).
% 4.77/1.85  tff(c_1431, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1397, c_1015])).
% 4.77/1.85  tff(c_1504, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_850, c_1431])).
% 4.77/1.85  tff(c_1505, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_50, c_1264, c_1504])).
% 4.77/1.85  tff(c_1550, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1505])).
% 4.77/1.85  tff(c_1553, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_850, c_40, c_1550])).
% 4.77/1.85  tff(c_1555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1553])).
% 4.77/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.85  
% 4.77/1.85  Inference rules
% 4.77/1.85  ----------------------
% 4.77/1.85  #Ref     : 0
% 4.77/1.85  #Sup     : 282
% 4.77/1.85  #Fact    : 0
% 4.77/1.85  #Define  : 0
% 4.77/1.85  #Split   : 4
% 4.77/1.85  #Chain   : 0
% 4.77/1.85  #Close   : 0
% 4.77/1.85  
% 4.77/1.85  Ordering : KBO
% 4.77/1.85  
% 4.77/1.85  Simplification rules
% 4.77/1.85  ----------------------
% 4.77/1.85  #Subsume      : 74
% 4.77/1.85  #Demod        : 583
% 4.77/1.85  #Tautology    : 61
% 4.77/1.85  #SimpNegUnit  : 129
% 4.77/1.85  #BackRed      : 0
% 4.77/1.85  
% 4.77/1.85  #Partial instantiations: 0
% 4.77/1.85  #Strategies tried      : 1
% 4.77/1.85  
% 4.77/1.85  Timing (in seconds)
% 4.77/1.85  ----------------------
% 4.77/1.86  Preprocessing        : 0.34
% 4.77/1.86  Parsing              : 0.18
% 4.77/1.86  CNF conversion       : 0.03
% 4.77/1.86  Main loop            : 0.74
% 4.77/1.86  Inferencing          : 0.29
% 4.77/1.86  Reduction            : 0.23
% 4.77/1.86  Demodulation         : 0.16
% 4.77/1.86  BG Simplification    : 0.03
% 4.77/1.86  Subsumption          : 0.14
% 4.77/1.86  Abstraction          : 0.04
% 4.77/1.86  MUC search           : 0.00
% 4.77/1.86  Cooper               : 0.00
% 4.77/1.86  Total                : 1.13
% 4.77/1.86  Index Insertion      : 0.00
% 4.77/1.86  Index Deletion       : 0.00
% 4.77/1.86  Index Matching       : 0.00
% 4.77/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
